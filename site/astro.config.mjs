// The results page: one static page built from src/data/results.json (written
// by prep/final.ts), or from src/data/sample.json when there is no run yet.
import { defineConfig } from "astro/config";

export default defineConfig({
  output: "static",
  build: { format: "file" },
});
