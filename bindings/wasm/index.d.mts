/* ESM-flavored declarations for the "import"/"browser" conditions
 * (index.mjs). The API shapes live in index.d.ts; re-exporting from a .d.mts
 * makes TypeScript under node16/nodenext treat the entry as a true ES module
 * — no synthesized default export that index.mjs doesn't have at runtime. */
export * from "./index.js";
