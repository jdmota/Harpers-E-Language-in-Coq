import * as fs from "fs/promises";
import * as path from "path";

const rules = [
  [
    "PFPL.Definitions.html",
    [
      /<span class="kwd">Inductive<\/span>\s*<span class="kwd">Eval<\/span>/,
      `<span class="kwd">Inductive</span> <span id="Eval" class="id">Eval</span>`
    ],
    [
      /<span class="kwd">Function<\/span>\s*<span class="id">alpha_equiv<\/span>/,
      `<span class="kwd">Function</span> <span id="alpha_equiv" class="id"><a href="PFPL.Definitions.html#alpha_equiv">alpha_equiv</a></span>`
    ],
    [
      /<span class="kwd">Fixpoint<\/span>\s*<span class="id">subst<\/span>'/,
      `<span class="kwd">Fixpoint</span> <span id="subst'" class="id">subst'</span>`
    ],
  ],
  [
    "PFPL.Theorems_Eval.html",
    [
      /<span class="kwd">Function<\/span>\s*<span class="id">eval_big<\/span>/,
      `<span class="kwd">Function</span> <span id="eval_big" class="id"><a href="PFPL.Theorems_Eval.html#eval_big">eval_big</a></span>`
    ]
  ],
  [
    /\.html$/,
    [
      /<span class="kwd">Eval<\/span>/g,
      `<span class="id"><a href="PFPL.Definitions.html#Eval">Eval</a></span>`
    ],
    [
      /<span class="id">alpha_equiv<\/span>/g,
      `<span class="id"><a href="PFPL.Definitions.html#alpha_equiv">alpha_equiv</a></span>`
    ],
    [
      /<span class="id">subst<\/span>'(?!<span class="id">)/g,
      `<span class="id"><a href="PFPL.Definitions.html#subst'">subst'</a></span>`
    ],
    [
      /<span class="id">eval_big<\/span>/g,
      `<span class="id"><a href="PFPL.Theorems_Eval.html#eval_big">eval_big</a></span>`
    ]
  ]
];

async function replace(name, replacements) {
  const file = path.resolve("./docs", name);
  let html = await fs.readFile(file, "utf-8");
  for (const [from, to] of replacements) {
    html = html.replace(from, to);
  }
  await fs.writeFile(file, html);
}

async function patch() {
  for (const [name, ...replacements] of rules) {
    if (typeof name === "string") {
      await replace(name, replacements);
    } else {
      const files = (await fs.readdir("./docs")).filter(f => name.test(f));
      for (const name of files) {
        await replace(name, replacements);
      }
    }
  }
}

patch();
