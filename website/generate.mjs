import * as fs from "fs/promises";
import * as path from "path";
import { BaseTopologicalOrder } from "./topological-order.mjs";

const character = "[a-zA-Z0-9_\\-$']";
const proofsKeywords = ["Lemma", "Theorem", "Corollary", "Instance"];
const statementsKeywords = [
  "Inductive", "Definition", "Fixpoint", "Program Fixpoint", "Function", ...proofsKeywords
];
const statementsSplitRegexp = new RegExp(statementsKeywords.map(k => `(^${k} [^\\.]+\\.)`).join("|"), "m");
const statementsExtractRegexp = statementsKeywords.map(
  k => new RegExp(`^(${k}) (${character}+)\\s*:?\\s*([^\\.]+)\\.`)
);
const proofRegexp = /^Proof.([^]+?)(?:Qed|Admitted)\./;
const proofSplitRegexp = /(\.|;|-|\+|\*|{|})/;
const tacticsRegexp = /^(all:\s+)?(try\s+)?(intro|intros|induction|constructor|assert|apply|subst|inversion|assumption|destruct|auto|lia|exists|remember|cut|split|generalize dependent|generalize|rewrite)/;

class TopologicalOrder extends BaseTopologicalOrder {
  constructor(database) {
    super();
    this.database = database;
  }

  inEdgesAmount(name) {
    return this.database.get(name).usedBy.size;
  }

  destinations(name) {
    return this.database.get(name).uses;
  }
}

class References {
  constructor() {
    this.map = new Map();
  }

  addRef(a, b) {
    if (a === b) {
      throw new Error(`self ref ${a}`);
    }
    this.map.get(a).uses.add(b);
    this.map.get(b).usedBy.add(a);
  }

  addRoot(lemmas) {
    this.addStatement("$root$", "Theorem", "$root$", "$root$", lemmas.map(l => `apply ${l}.`).join("\n"))
  }

  addStatement(file, type, name, statement, proof) {
    if (!proofsKeywords.includes(type)) {
      // Ignore definitions
      return;
    }
    this.map.set(name, {
      file,
      type,
      name,
      statement,
      proof,
      proofLines: proof?.split("\n").length,
      uses: new Set(),
      usedBy: new Set(),
      transitiveUses: null,
      transitiveUsedBy: null,
    });
  }

  get(name) {
    return this.map.get(name);
  }

  transitiveUses(name, stack = new Set()) {
    const ref = this.get(name);
    if (ref.transitiveUses)
      return ref.transitiveUses;
    if (stack.has(name))
      return new Set();
    stack.add(name);

    const set = new Set();
    for (const dep of ref.uses) {
      set.add(dep);
      for (const r of this.transitiveUses(dep, stack))
        set.add(r);
    }
    ref.transitiveUses = set;
    return set;
  }

  transitiveUsedBy(name, stack = new Set()) {
    const ref = this.get(name);
    if (ref.transitiveUsedBy)
      return ref.transitiveUsedBy;
    if (stack.has(name))
      return new Set();
    stack.add(name);

    const set = new Set();
    for (const dep of ref.usedBy) {
      set.add(dep);
      for (const r of this.transitiveUsedBy(dep, stack))
        set.add(r);
    }
    ref.transitiveUsedBy = set;
    return set;
  }

  // TODO track things like eval_big_ind? Note that these kinds of things are not generated by us...
  connect() {
    const regexp = new RegExp(`(?<!${character})(${Array.from(this.map.keys()).join("|")})(?!${character})`, "g");

    for (const {type, name, statement, proof} of this.map.values()) {
      /*for (const [, ref] of statement.matchAll(regexp)) {
        this.addRef(name, ref);
      }*/

      if (proof) {
        const proofParts = proof
          // Remove occurrences of <- and -> first
          // Because proofSplitRegexp splits the -
          .replace(/rewrite\s*<-/g, "rewrite ") 
          .replace(/rewrite\s*->/g, "rewrite ")
          .split(proofSplitRegexp)
          .map(l => l.trim().replace(tacticsRegexp, "").trim())
          .filter(l => l.length > 1);

        for (const proofPart of proofParts) {
          for (const [, ref] of proofPart.matchAll(regexp)) {
            this.addRef(name, ref);
          }
        }
      }
    }
  }

  print() {
    for (const {type, name, statement, uses, usedBy} of this.map.values()) {
      console.log({
        type,
        name,
        statement,
        uses,
        usedBy
      });
    }
  }

  topologicalOrder() {
    return new TopologicalOrder(this).process(this.map.keys());
  }

  [Symbol.iterator]() {
    return this.map.values();
  }

  static database = new References();
}

async function findCoqFiles() {
  return (await fs.readdir("coq")).filter(f => f.endsWith(".v"));
}

function read(file) {
  return fs.readFile(file, "utf-8");
}

async function processCoqFile(file) {
  const content = await read(`coq/${file}`);
  const parts = content.split(statementsSplitRegexp).map(s => s?.trim()).filter(Boolean);
  for (let i = 0; i < parts.length; i++) {
    const part = parts[i];
    const match = statementsExtractRegexp.reduce((acc, regexp) => (acc ?? part.match(regexp)), null);
    if (match) {
      const [, type, name, statement] = match;
      const [, proof] = parts[i + 1]?.match(proofRegexp) ?? [null, null];
      References.database.addStatement(file, type, name, statement.trim().replace(/\s+/g, " "), proof?.trim());
      if (proof) {
        i++;
      }
    }
  }
}

async function processCoqFiles() {
  const coqFiles = await findCoqFiles();
  for (const file of coqFiles) {
    await processCoqFile(file);
  }

  const metadata = JSON.parse(await read("website/metadata.json"));

  References.database.addRoot([
    ...metadata.harpersBook,
    ...metadata.original
  ]);

  References.database.connect();
  // References.database.print();

  const notUsed = [];
  const taxonomyData = [];
  for (const {name, file, type, statement, proofLines, uses, usedBy} of References.database) {
    if (proofsKeywords.includes(type)) {
      if (usedBy.size) {
        taxonomyData.push({
          name,
          file,
          type,
          statement,
          proofLines,
          uses: Array.from(uses),
          usedBy: Array.from(usedBy).filter(r => r !== "$root$"),
          transitiveUses: References.database.transitiveUses(name).size,
          transitiveUsedBy: References.database.transitiveUsedBy(name).size - (usedBy.has("$root$") ? 1 : 0),
        });
      } else if (name !== "$root$") {
        notUsed.push(name);
      }
    }
  }
  console.log("Not used:", notUsed);
  return {
    coqFiles,
    metadata,
    taxonomyData
  };
}

async function generateWebsite() {
  const {coqFiles, metadata, taxonomyData} = await processCoqFiles();

  await fs.writeFile("docs/taxonomy_data.js", `// This file was automatically generated. Do not edit.\nconst taxonomyData = ${JSON.stringify(taxonomyData)};\nconst taxonomyMetadata = ${JSON.stringify(metadata)};\n`);

  await fs.copyFile("website/taxonomy.html", "docs/taxonomy.html");

  const indexFile = await read("website/index.html");

  await fs.writeFile("docs/index.html", indexFile.replace("<!--LIST-->", coqFiles.map(f =>
    `<div><a href="PFPL.${f.replace(/\.v$/, "")}.html">${f}</a></div>`
  ).join("\n")));
}

generateWebsite();
