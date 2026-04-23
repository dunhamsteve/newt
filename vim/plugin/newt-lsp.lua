vim.lsp.config['newt'] = {
	-- we'll change this to a newt-lsp wrapper later
	cmd =  { 'newt-lsp', '--stdio' },
	filetypes = { 'newt' },
	root_markers = { '.git' }
}
vim.lsp.enable('newt')
