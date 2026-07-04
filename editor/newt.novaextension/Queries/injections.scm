((jsStringFragment) @injection.content
  (#set! injection.language "javascript"))

; zed used content/language instead of the @injection versions
; and this still doesn't work..
((jsStringFragment) @content
  (#set! "language" "javascript")
  (#set! "combined"))
