# Generating Latex snippets from VeracityLogic.v

`generate-coq-snippets.sh` generates Latex for snippets surrounded by markup in VeracityLogic.v
They are generated in the folder `./coq-snippets` along with the assets required in the `./coq-snippets/assets` folder.

Markup is:

```
(* begin snippet SNIPPET-NAME *)
... COQ CODE ...
(* end snippet SNIPPET-NAME *)
```

The Coq code can also be annotated to indicate when it should be unfolded etc, as described at:
  https://github.com/cpitclaudel/alectryon?tab=readme-ov-file#controlling-output

The generated snippets can then be included in Latex by, for example:

```
\inputsnippets{SNIPPET-NAME.tex}
```

However, some definitions are required for this, in particular:

This must be added to the Latex preamble:

```
\usepackage{texments}
%%% for movies by alectryon
\usepackage{./coq-snippets/assets/alectryon}
\usepackage{./coq-snippets/assets/pygments}

% Prevent breaks in the middle of syntactic units
\let\OldPY\PY
\def\PY#1#2{\OldPY{#1}{\mbox{#2}}}


%%% One hypothesis per line 
\makeatletter
\renewcommand{\alectryon@hyps@sep}{\alectryon@nl}
\makeatother

\makeatletter
\newcommand{\pathtomovies}{./coq-snippets}
\newcommand{\inputsnippets}[1]
  {{\setlength{\itemsep}{1pt}\setlength{\parsep}{0pt}% Adjust spacing
    \alectryon@copymacros\begin{io}
      \forcsvlist{\item\@inputsnippet}{#1}
    \end{io}}}
\let\input@old\input % Save definition of \input
\newcommand{\@inputsnippet}[1]
  {{\renewenvironment{alectryon}{}{}% Skip \begin{alectryon} included in snippet
    \input@old{{\pathtomovies}/#1}}}
\makeatother
```
Based on `hydras.tex` from the coq-community/hydra-battles GitHub repository, used under the [MIT license](https://github.com/coq-community/hydra-battles/blob/1c30f04ac1e855ffae43c044bb7d4fa16a14af71/LICENSE).