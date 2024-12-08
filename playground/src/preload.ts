import {ZipFile} from './zipfile'
export let archive: ZipFile | undefined;
export let preload = (async function () {
  // We pull down an archive of .ttc and support shim.files
  try {
    let res = await self.fetch("files.zip");
    if (res.status === 200) {
      let data = await res.arrayBuffer();
      archive = new ZipFile(new Uint8Array(data));
      let entries = archive.entries;
      let count = Object.keys(entries).length;
      console.log(`preloaded ${count} files`);
    } else {
      console.error(
        `fetch of files.zip got status ${res.status}: ${res.statusText}`
      );
    }
  } catch (e) {
    console.error("preload failed", e);
  }
})();
