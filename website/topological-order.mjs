// type Node<V> = { value: V; next: Node<V> | null };

class Queue {
  head = null;
  tail = null;

  enqueue(value) {
    const node = { value, next: null };
    if (this.tail) {
      this.tail.next = node;
    } else {
      this.head = node;
    }
    this.tail = node;
  }

  dequeue() {
    if (!this.head) return null;
    const value = this.head.value;
    this.head = this.head.next;
    if (!this.head) this.tail = null;
    return value;
  }
}

// Assuming the nodes considered form a DAG

export class BaseTopologicalOrder {
  inEdgesAmount(node) {
    throw new Error("inEdgesAmount");
  }

  destinations(node) {
    throw new Error("destinations");
  }

  *process(nodes) {
    const queue = new Queue();
    const inEdgesMap = new Map();

    for (const n of nodes) {
      const inEdges = this.inEdgesAmount(n);
      inEdgesMap.set(n, inEdges);
      if (inEdges === 0) {
        queue.enqueue(n);
      }
    }

    while (true) {
      const node = queue.dequeue();
      if (!node) break;
      yield node;

      for (const dest of this.destinations(node)) {
        const inEdges = inEdgesMap.get(dest) - 1;
        inEdgesMap.set(dest, inEdges);
        if (inEdges === 0) {
          queue.enqueue(dest);
        }
      }
    }

    /*console.log("CIRCULAR");
    for (const [name, count] of inEdgesMap) {
      if (count > 0) console.log(this.database.map.get(name));
    }*/
  }
}
