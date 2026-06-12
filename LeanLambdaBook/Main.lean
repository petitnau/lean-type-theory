import VersoManual
import LeanLambdaBook.Book

open Verso.Genre.Manual

def bookConfig : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  destination := "_out/book"
  htmlDepth := 2

def main := manualMain (%doc LeanLambdaBook.Book) (config := bookConfig)
