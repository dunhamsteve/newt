vim.lsp.config['newt'] = {
	cmd =  { 'newt-lsp', '--stdio' },
	filetypes = { 'newt', 'markdown.newt' },
	root_markers = { '.git' }
}
vim.lsp.enable('newt')
