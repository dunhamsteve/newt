import {checkFile, showActions, rename} from '../tests/utils.js'

checkFile('LSPStuff.newt')
showActions('LSPStuff.newt', 5, 6)
showActions('LSPStuff.newt', 5, 12)
showActions('LSPStuff.newt', 9, 0)
showActions('LSPStuff.newt', 12, 5)
showActions('LSPStuff.newt', 16, 12)
rename('LSPStuff.newt', 20, 17, 'woot')
rename('LSPStuff.newt', 27, 20, 'woot')
