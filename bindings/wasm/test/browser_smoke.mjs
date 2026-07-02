/* Browser gate (B5): vite-build the test app against the *installed*
 * kome-sync package, serve the output, load it in headless Chromium, and
 * assert the in-page convergence reported KOME_OK.
 *
 * Copy into (and run from) a project directory where kome-sync, vite, and
 * playwright are installed (run `npx playwright install chromium` once) —
 * ESM resolves imports relative to this file, so it must live inside the
 * project:
 *   cp -r <repo>/bindings/wasm/test/browser <repo>/bindings/wasm/test/browser_smoke.mjs .
 *   node browser_smoke.mjs browser
 *
 * Chromium: playwright's own managed browser, unless $CHROMIUM_BIN overrides.
 */
import { createServer } from "node:http";
import { readFile } from "node:fs/promises";
import path from "node:path";
import { build } from "vite";
import { chromium } from "playwright";

const root = path.resolve(process.argv[2] || "browser");
const outDir = path.join(root, "dist");

await build({ root, base: "./", build: { outDir, emptyOutDir: true }, logLevel: "warn" });

const MIME = {
  ".html": "text/html",
  ".js": "text/javascript",
  ".mjs": "text/javascript",
  ".wasm": "application/wasm",
};
const srv = createServer(async (req, res) => {
  const rel = req.url === "/" ? "index.html" : req.url.split("?")[0].slice(1);
  try {
    const data = await readFile(path.join(outDir, rel));
    res.writeHead(200, { "content-type": MIME[path.extname(rel)] || "application/octet-stream" });
    res.end(data);
  } catch {
    res.writeHead(404);
    res.end();
  }
});
await new Promise((r) => srv.listen(0, "127.0.0.1", r));
const url = `http://127.0.0.1:${srv.address().port}/`;

const launchOpts = { args: ["--no-sandbox"] };
if (process.env.CHROMIUM_BIN) launchOpts.executablePath = process.env.CHROMIUM_BIN;
const browser = await chromium.launch(launchOpts);
try {
  const page = await browser.newPage();
  page.on("pageerror", (e) => console.error("[pageerror]", e.message));
  await page.goto(url);
  await page.waitForFunction(
    () => document.title === "KOME_OK" || document.title === "KOME_FAIL",
    { timeout: 30000 });
  const title = await page.title();
  if (title !== "KOME_OK") {
    console.error("browser smoke FAILED:", await page.locator("#out").textContent());
    process.exit(1);
  }
  console.log("browser smoke: OK (vite build, headless chromium)");
} finally {
  await browser.close();
  srv.close();
}
