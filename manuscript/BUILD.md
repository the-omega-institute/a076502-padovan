# LaTeX source for the merged research note

Main document: `paper.tex`.

The source archive contains one manuscript, with verification appendices
S1--S3 in the same document. It includes `appendix-body.tex` and all three
tables in `generated/`. There is no separate supplement to compile or upload.
The title is "A Padovan-automatic description of a nested recurrence";
authors are Benoit Cloitre, Haobo Ma, and Wenlin Zhang in alphabetical order.

Extract the archive and run the following command three times from its root:

```sh
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```

The supplied manuscript is 14 pages. The source uses article, AMS mathematics,
Latin Modern and newtx fonts, geometry, microtype, booktabs, enumitem, xcolor,
fancyhdr, hyperref and cleveref. Use a TeX installation with these packages.
References are embedded in the source; BibTeX, Python, Lean, and the private
collaboration workspace are not needed to compile it. In Overleaf or arXiv,
select `paper.tex` as the main document. `SHA256SUMS.json` records archive
member hashes and is not a manuscript input.

The manuscript contains the confirmed author affiliations and emails and the
AI-use disclosure, including GPT-5.6 and GPT-6 Astra for H.M. and W.Z.
Final author review remains necessary before submission.

The separately supplied `a076502-research-supplement.zip` is a reproducibility
package for the mathematical computations and formal proofs. It is not
required to compile or submit this LaTeX source. Its root `README.md` explains
the checks and distinguishes archived Lean validation from a new run.
