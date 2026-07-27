import {checkFile, showActions} from '../tests/utils.js'

checkFile('LSPStuff.newt')
showActions('LSPStuff.newt', 5, 6)
showActions('LSPStuff.newt', 5, 12)
showActions('LSPStuff.newt', 9, 0)
showActions('LSPStuff.newt', 12, 5)

