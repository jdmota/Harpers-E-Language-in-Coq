cd coq
../coq2html-1.2/coq2html.exe *.glob *.v -base PFPL -d ../docs
cd ..
node website/generate.mjs
