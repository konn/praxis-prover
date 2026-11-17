// Dynamic import lets startup failures be returned through the JSON protocol.
const runtime = import("./runtime.js").then(({ loadPraxis }) => loadPraxis());
let pending = Promise.resolve();
self.addEventListener("message", ({ data }) => {
  // Serialize calls into one GHC runtime. Keeping it in a worker also keeps
  // rendering and keyboard interaction responsive during evaluation.
  pending = pending.then(async () => {
    try {
      const evaluate = await runtime;
      self.postMessage({ id: data.id, response: await evaluate(data.request) });
    } catch (error) {
      self.postMessage({ id: data.id, response: { error: { message: String(error) } } });
    }
  });
});
