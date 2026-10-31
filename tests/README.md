
The test runner is `./scripts/test`. We can also `make test`

- Anything ending in .newt or .newt.md is a test.
- If `Foo.newt.skip` exists, the test is skipped
- If `Foo.newt.golden` exists, the file is compiled to js, the result is run and compared to golden.
- If `Foo.newt.fail` exists, the file checked, failure is expected, and the output is compared to .fail
- If `Foo.newt.js` exists, that is run instead of the output. 
  - This is used for testing the LSP, the js will run the functions backing the LSP and output compared to golden.
- `./script/tests Foo` will only run tests containing `Foo`.
- `./script/tests -u` will update snapshots.
- `make tests update=true` will update snapshots.

