vim.lsp.config['newt_ls'] = {
	-- we'll change this to a newt-lsp wrapper later
	cmd =  { 'node', 'newt-vscode-lsp/dist/lsp.js', '--stdio' },
	filetypes = { 'newt' },
	root_markers = { '.git' }
}
vim.lsp.enable('newt_ls')
