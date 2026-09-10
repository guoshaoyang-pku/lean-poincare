import { defineConfig } from "vite";

export default defineConfig({
  base: "./",
  build: {
    // The 3D renderer is a lazy chunk and is never part of the initial page load.
    chunkSizeWarningLimit: 600,
  },
});
