import VersoManual
import LeanLambdaBook.Book

open Verso.Genre.Manual

def courseCss : CSS := r#"
:root {
  --verso-toc-width: 16rem;
  --verso-toc-background-color: #fbfbfa;
  --verso-content-max-width: 54rem;
  --verso-code-keyword-color: #7a2f8f;
  --verso-code-const-color: #174e7a;
  --verso-code-var-color: #4b5563;
  --verso-code-color: #1f2937;
}

body {
  background: #f7f7f4;
}

header {
  border-bottom: 1px solid #e2dfd7;
  box-shadow: none;
}

.header-title {
  font-size: 1.45rem;
}

.content-wrapper {
  background: #fff;
  min-height: calc(100dvh - var(--verso-header-height));
  padding-top: 2rem;
  padding-bottom: 4rem;
}

main h1 {
  font-size: 2rem;
  line-height: 1.18;
  margin-top: 0.75rem;
}

main h2 {
  font-size: 1.35rem;
}

main p {
  font-size: 1rem;
  line-height: 1.62;
}

main a {
  color: #145ea8;
  text-decoration-thickness: 0.08em;
  text-underline-offset: 0.16em;
}

code:not(.hl) {
  background: #f0efe9;
  border: 1px solid #dfddd4;
  border-radius: 0.25rem;
  color: #1f2937;
  font-size: 0.92em;
  padding: 0.05rem 0.22rem;
}

.hl.lean.block {
  background: #f7f7f2;
  border: 1px solid #dedbd2;
  border-left: 0.26rem solid #6c8ca6;
  border-radius: 0.35rem;
  box-shadow: 0 1px 0 rgba(0, 0, 0, 0.03);
  box-sizing: border-box;
  display: block;
  font-size: 0.94rem;
  line-height: 1.55;
  margin: 1rem 0;
  max-width: 100%;
  overflow-x: auto;
  padding: 0.85rem 1rem;
}

.hl.lean.block:has(+ .hl.lean.block) {
  border-bottom-color: transparent;
  border-bottom-left-radius: 0;
  border-bottom-right-radius: 0;
  margin-bottom: 0;
  padding-bottom: 0.35rem;
}

.hl.lean.block + .hl.lean.block {
  border-top-color: transparent;
  border-top-left-radius: 0;
  border-top-right-radius: 0;
  margin-top: 0;
  padding-top: 0.35rem;
}

.hl.lean.block + .hl.lean.block:has(+ .hl.lean.block) {
  border-radius: 0;
}

.hl.lean.block + .hl.lean.block:not(:has(+ .hl.lean.block)) {
  border-bottom-left-radius: 0.35rem;
  border-bottom-right-radius: 0.35rem;
}

.hl.lean .keyword {
  font-weight: 700;
}

.hl.lean .module-name,
.hl.lean .const {
  font-weight: 600;
}

.prev-next-buttons {
  border-bottom: 1px solid #e5e2da;
  display: grid;
  font-size: 0.9rem;
  gap: 1rem;
  grid-template-columns: 1fr 1fr;
  margin-bottom: 1.5rem;
  padding-bottom: 0.65rem;
}

.prev-next-buttons .local-button {
  background: transparent;
  border: 0;
  border-radius: 0;
  color: #4b5563;
  padding: 0.15rem 0;
}

.prev-next-buttons .local-button:hover {
  color: #111827;
  text-decoration: none;
}

.prev-next-buttons .local-button .where {
  margin: 0 0.2rem;
  top: 0;
}

.prev-next-buttons .arrow {
  color: #6c8ca6;
  font-size: 1rem;
}

main ol.section-toc {
  background: transparent;
  border-top: 1px solid #e5e2da;
  border-bottom: 1px solid #e5e2da;
  margin: 1.5rem 0 1.8rem 0;
  padding: 0.8rem 0 0.8rem 3rem;
}

main .section-toc li {
  font-size: 0.96rem;
  line-height: 1.45;
  margin-left: 0.5rem;
}

#toc {
  border-right: 1px solid #e5e2dc;
}

#toc .split-tocs {
  margin-top: 0.75rem;
  padding: 0 0.85rem 1rem 0.85rem;
}

#toc .split-toc {
  margin-bottom: 1.1rem;
  font-size: 0.88rem;
  line-height: 1.28;
}

#toc .split-toc.book {
  margin-bottom: 1.4rem;
}

#toc .split-toc .title {
  color: #555;
  font-size: 0.78rem;
  font-weight: 700;
  letter-spacing: 0.04em;
  text-transform: uppercase;
}

#toc .split-toc label.toggle-split-toc::before {
  background-color: #777;
  transform: scale(0.75);
}

#toc .split-toc table,
#toc .split-toc > ol {
  border-left: 0;
  margin-left: 0;
  padding-left: 0.15rem;
}

#toc .split-toc table {
  border-spacing: 0 0.2rem;
}

#toc .split-toc td.num {
  color: #777;
  padding-right: 0.35rem;
}

#toc .split-toc > ol {
  font-size: 0.88rem;
  margin-top: 0.45rem;
}

#toc .split-toc > ol > li {
  padding-left: 1.9rem;
  text-indent: -1.9rem;
  margin-bottom: 0.18rem;
}

#toc .split-toc .current td:not(.num),
#toc .split-toc .title .current {
  text-decoration: none;
  font-weight: 700;
}
"#

def bookConfig : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  destination := "_out/book"
  htmlDepth := 2
  extraCss := {courseCss}

def main := manualMain (%doc LeanLambdaBook.Book) (config := bookConfig)
