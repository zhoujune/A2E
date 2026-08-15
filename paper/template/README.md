# FSE 2027 Research Track LaTeX Template

FSE 2027 Research Papers requires the ACM `acmsmall` single-column layout.
The CFP recommends:

```latex
\documentclass[acmsmall,screen,review,anonymous]{acmart}
```

The initial submission limit is 18 pages for text and figures, plus 4 pages
for references. The submission must be double-anonymous and include a
`Data Availability` section after the conclusion.

## Official package

`acmart-primary-2.19-source.zip` is the production ACM/CTAN source package,
matching the version listed by the FSE 2027 CFP. It contains `acmart.dtx`,
`acmart.ins`, and the sample source distribution. The generated `acmart.cls`
and `sample-acmsmall-conf.tex` are produced by TeX from these sources; they
are intentionally not hand-copied or modified here.

Source: <https://mirrors.ctan.org/macros/latex/contrib/acmart.zip>

The package SHA-256 is recorded in `sources.sha256`.

## Generate the class and samples

With TeX Live or MiKTeX installed, unpack the source package and run:

```sh
unzip acmart-primary-2.19-source.zip
cd acmart
latex acmart.ins
cd samples
latex samples.ins
```

Use the generated files in the manuscript directory. Do not change ACM
margins, fonts, or the `acmsmall` layout.
