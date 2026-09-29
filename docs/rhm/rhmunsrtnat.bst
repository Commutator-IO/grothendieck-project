%% File: `rhmnat.bst'
%% A modification of `unsrtnat.bst' for use with natbib package 
%%
%% Copyright 1993-1999 Patrick W Daly
%% Max-Planck-Institut f\"ur Aeronomie
%% Max-Planck-Str. 2
%% D-37191 Katlenburg-Lindau
%% Germany
%% E-mail: daly@linmpi.mpg.de
%%
%% This program can be redistributed and/or modified under the terms
%% of the LaTeX Project Public License Distributed from CTAN
%% archives in directory macros/latex/base/lppl.txt; either
%% version 1 of the License, or any later version.
%%
 % Version and source file information:
 % \ProvidesFile{natbst.mbs}[2003/06/06 1.7 (PWD)]
 %
 % BibTeX `plainnat' family
 %   version 0.99b for BibTeX versions 0.99a or later,
 %   for LaTeX versions 2.09 and 2e.
 %
 % For use with the `natbib.sty' package; emulates the corresponding
 %   member of the `plain' family, but with author-year citations.
 %
 % With version 6.0 of `natbib.sty', it may also be used for numerical
 %   citations, while retaining the commands \citeauthor, \citefullauthor,
 %   and \citeyear to print the corresponding information.
 %
 % For version 7.0 of `natbib.sty', the KEY field replaces missing
 %   authors/editors, and the date is left blank in \bibitem.
 %
 % Includes field EID for the sequence/citation number of electronic journals
 %  which is used instead of page numbers.
 %
 % Includes fields ISBN and ISSN.
 %
 % Includes field URL for Internet addresses.
 %
 % Includes field DOI for Digital Object Idenfifiers.
 %
 % Works best with the url.sty package of Donald Arseneau.
 %
ENTRY
  { address
    author
    booktitle
    chapter
    doi
    eid
    edition
    editor
    etiquette
    howpublished
    institution
    isbn
    issn
    journal
    key
    month
    note
    number
    organization
    othernote
    pages
    publisher
    school
    series
    title
    type
    url
    volume
    year
  }
  {}
  { label extra.label sort.label short.list }

INTEGERS { output.state before.all mid.sentence after.sentence after.block }

FUNCTION {init.state.consts}
{ #0 'before.all :=
  #1 'mid.sentence :=
  #2 'after.sentence :=
  #3 'after.block :=
}

STRINGS { s t }

FUNCTION {output.nonnull}
{ 's :=
  output.state mid.sentence =
    { ", " * write$ }
    { output.state after.block =
        { ", " * write$ }
        { output.state before.all =
            'write$
            { ", " * write$ }
          if$
        }
      if$
      mid.sentence 'output.state :=
    }
  if$
  s
}

FUNCTION {output.nonnullb}
{ 's :=
  output.state mid.sentence =
    { ", " * write$ }
    { output.state after.block =
        { write$
          newline$
          "\newblock " write$
        }
        { output.state before.all =
            'write$
            { " " * write$ }
          if$
        }
      if$
      mid.sentence 'output.state :=
    }
  if$
  s
}

FUNCTION {output.nonnullc}
{ 's :=
  output.state mid.sentence =
    { "; " * write$ }
    { output.state after.block =
        { write$
          newline$
          "\newblock " write$
        }
        { output.state before.all =
            'write$
            { " " * write$ }
          if$
        }
      if$
      mid.sentence 'output.state :=
    }
  if$
  s
}

FUNCTION {output.nonnulld}
{ 's :=
  output.state mid.sentence =
    { ": " * write$ }
    { output.state after.block =
        { write$
          newline$
          "\newblock " write$
        }
        { output.state before.all =
            'write$
            { " " * write$ }
          if$
        }
      if$
      mid.sentence 'output.state :=
    }
  if$
  s
}

FUNCTION {output.nonnulle}
{ 's :=
  output.state mid.sentence =
    { " " * write$ }
    { output.state after.block =
        { " " * write$ }
        { output.state before.all =
            'write$
            { " " * write$ }
          if$
        }
      if$
      mid.sentence 'output.state :=
    }
  if$
  s
}

FUNCTION {output}
{ duplicate$ empty$
    'pop$
    'output.nonnullb
  if$
}

FUNCTION {outputc}
{ duplicate$ empty$
    'pop$
    'output.nonnullc
  if$
}

FUNCTION {outputd}
{ duplicate$ empty$
    'pop$
    'output.nonnulld
  if$
}

FUNCTION {outpute}
{ duplicate$ empty$
    'pop$
    'output.nonnulle
  if$
}

FUNCTION {output.check}
{ 't :=
  duplicate$ empty$
    { pop$ "empty " t * " in " * cite$ * warning$ }
    'output.nonnull
  if$
}

FUNCTION {output.checkb}
{ 't :=
  duplicate$ empty$
    { pop$ "empty " t * " in " * cite$ * warning$ }
    'output.nonnullb
  if$
}

FUNCTION {output.checkdd}
{ 't :=
  duplicate$ empty$
    { pop$ "empty " t * " in " * cite$ * warning$ }
    'output.nonnulld
  if$
}

FUNCTION {output.checkd}
{ address empty$
   { output.checkb }
   { output.checkdd }
  if$
}

FUNCTION {output.checke}
{ 't :=
  duplicate$ empty$
    { pop$ "empty " t * " in " * cite$ * warning$ }
    'output.nonnulle
  if$
}

FUNCTION {fin.entry}
{ add.period$
  write$
  newline$
}

FUNCTION {new.block}
{ output.state before.all =
    'skip$
    { after.block 'output.state := }
  if$
}

FUNCTION {new.sentence}
{ output.state after.block =
    'skip$
    { output.state before.all =
        'skip$
        { after.sentence 'output.state := }
      if$
    }
  if$
}

FUNCTION {not}
{   { #0 }
    { #1 }
  if$
}

FUNCTION {and}
{   'skip$
    { pop$ #0 }
  if$
}

FUNCTION {or}
{   { pop$ #1 }
    'skip$
  if$
}

FUNCTION {new.block.checka}
{ empty$
    'skip$
    'new.block
  if$
}

FUNCTION {new.block.checkb}
{ empty$
  swap$ empty$
  and
    'skip$
    'new.block
  if$
}

FUNCTION {new.sentence.checka}
{ empty$
    'skip$
    'new.sentence
  if$
}

FUNCTION {new.sentence.checkb}
{ empty$
  swap$ empty$
  and
    'skip$
    'new.sentence
  if$
}

FUNCTION {field.or.null}
{ duplicate$ empty$
    { pop$ "" }
    'skip$
  if$
}

FUNCTION {emphasize}
{ duplicate$ empty$
    { pop$ "" }
    { "\emph{" swap$ * "}" * }
  if$
}

FUNCTION {smallcaps}
{ duplicate$ empty$
    { pop$ "" }
    { "\textsc{" swap$ * "}" * }
  if$
}


INTEGERS { nameptr namesleft numnames }

FUNCTION {format.names}
{ 's :=
  #1 'nameptr :=
  s num.names$ 'numnames :=
  numnames 'namesleft :=
    { namesleft #0 > }
    { s nameptr "{vv~}{ll}" format.name$ smallcaps
      s nameptr "{~(ff)}{, jj}" format.name$ * 't :=
      nameptr #1 >
        { namesleft #1 >
            { ", " * t * }
            { numnames #2 >
                { "" * }
                'skip$
              if$
              t "\textsc{others}" =
                { " et~al." * }
                { " \smfandname\ " * t * }
              if$
            }
          if$
        }
        't
      if$
      nameptr #1 + 'nameptr :=
      namesleft #1 - 'namesleft :=
    }
  while$
}

FUNCTION {format.names.ed}
{ 's :=
  #1 'nameptr :=
  s num.names$ 'numnames :=
  numnames 'namesleft :=
    { namesleft #0 > }
    { s nameptr "{vv~}{ll}" format.name$
      s nameptr "{~(ff)}{, jj}" format.name$ * 't :=
      nameptr #1 >
        { namesleft #1 >
            { ", " * t * }
            { numnames #2 >
                { "" * }
                'skip$
              if$
              t "\textsc{others}" =
                { " et~al." * }
                { " \smfandname\ " * t * }
              if$
            }
          if$
        }
        't
      if$
      nameptr #1 + 'nameptr :=
      namesleft #1 - 'namesleft :=
    }
  while$
}

%FUNCTION {format.names.editors}
%{ 's :=
%  #1 'nameptr :=
%  s num.names$ 'numnames :=
%  numnames 'namesleft :=
%    { namesleft #0 > }
%    { s nameptr "{f.~}{vv~}{ll}{, jj}" format.name$ 't :=
%      nameptr #1 >
%        { namesleft #1 >
%            { ", " * t * }
%            { numnames #2 >
%                { "" * }
%                'skip$
%              if$
%              t "others" =
%                { " et~al." * }
%                { " \smfandname\ " * t * }
%              if$
%            }
%          if$
%        }
%        't
%      if$
%      nameptr #1 + 'nameptr :=
%      namesleft #1 - 'namesleft :=
%    }
%  while$
%}

FUNCTION {format.key}
{ empty$
    { key field.or.null }
    { "" }
  if$
}

FUNCTION {format.authors}
{ author empty$
    { "" }
    { author format.names }
  if$
}

FUNCTION {format.editors.authors}
{ editor empty$
    { "" }
    { editor format.names
      editor num.names$ #1 >
        { ", \smfedsname" * }
        { ", \smfedname" * }
      if$
    }
  if$
}

%FUNCTION {format.editors}
%{ editor empty$
%    { "" }
%    { editor format.names.editors
%      editor num.names$ #1 >
%        { ", \smfedsname" * }
%        { ", \smfedname" * }
%      if$
%    }
%  if$
%}

FUNCTION {format.ed}
{ editor empty$
    { "" }
    { editor format.names.ed
      editor num.names$ #1 >
        { ", \smfedsname" * }
        { ", \smfedname" * }
      if$
    }
  if$
}

FUNCTION {format.editedby}
{ editor empty$
    { "" }
    { "\smfedbyname\ " editor format.names.ed * }
  if$
}

FUNCTION {format.isbn}
{ isbn empty$
    { "" }
    { new.block "ISBN " isbn * }
  if$
}

FUNCTION {format.issn}
{ issn empty$
    { "" }
    { new.block "ISSN " issn * }
  if$
}

FUNCTION {format.url}
{ url empty$
    { "" }
    { new.block "URL \url{" url * "}" * }
  if$
}

FUNCTION {format.doi}
{ doi empty$
    { "" }
    { new.block "\doi{" doi * "}" * }
  if$
}

FUNCTION {format.title}
{ title empty$
    { "" }
    { title "t" change.case$ }
  if$
}

FUNCTION {format.full.names}
{'s :=
  #1 'nameptr :=
  s num.names$ 'numnames :=
  numnames 'namesleft :=
    { namesleft #0 > }
    { s nameptr
      "{vv~}{ll}" format.name$ 't :=
      nameptr #1 >
        {
          namesleft #1 >
            { ", " * t * }
            {
              numnames #2 >
                { "" * }
                'skip$
              if$
              t "others" =
                { " et~al." * }
                { " \smfandname\ " * t * }
              if$
            }
          if$
        }
        't
      if$
      nameptr #1 + 'nameptr :=
      namesleft #1 - 'namesleft :=
    }
  while$
}

FUNCTION {author.editor.full}
{ author empty$
    { editor empty$
        { "" }
        { editor format.full.names }
      if$
    }
    { author format.full.names }
  if$
}

FUNCTION {author.full}
{ author empty$
    { "" }
    { author format.full.names }
  if$
}

FUNCTION {editor.full}
{ editor empty$
    { "" }
    { editor format.full.names }
  if$
}

FUNCTION {make.full.names}
{ type$ "book" =
  type$ "inbook" =
  or
    'author.editor.full
    { type$ "proceedings" =
        'editor.full
        'author.full
      if$
    }
  if$
}

FUNCTION {output.bibitem}
{ newline$
  "\bibitem[" write$
  label write$
  ")" make.full.names duplicate$ short.list =
     { pop$ }
     { * }
   if$
  "]{" * write$
  cite$ write$
  "}" write$
  newline$
  ""
  before.all 'output.state :=
}

FUNCTION {n.dashify}
{ 't :=
  ""
    { t empty$ not }
    { t #1 #1 substring$ "-" =
        { t #1 #2 substring$ "--" = not
            { "--" *
              t #2 global.max$ substring$ 't :=
            }
            {   { t #1 #1 substring$ "-" = }
                { "-" *
                  t #2 global.max$ substring$ 't :=
                }
              while$
            }
          if$
        }
        { t #1 #1 substring$ *
          t #2 global.max$ substring$ 't :=
        }
      if$
    }
  while$
}

FUNCTION {format.date}
{ year duplicate$ empty$
    { "empty year in " cite$ * warning$
       pop$ "" }
    'skip$
  if$
  month empty$
    'skip$
    { month
      " " * swap$ *
    }
  if$
  extra.label *
}

FUNCTION {format.date.nolabel}
{ year duplicate$ empty$
    { "empty year in " cite$ * warning$
       pop$ "" }
    'skip$
  if$
  month empty$
    'skip$
    { month
      " " * swap$ *
    }
  if$
}

FUNCTION {format.btitle}
{ title emphasize
}

FUNCTION {tie.or.space.connect}
{ duplicate$ text.length$ #3 <
    { "\kern2pt " }
    { " " }
  if$
  swap$ * *
}

FUNCTION {either.or.check}
{ empty$
    'pop$
    { "can't use both " swap$ * " fields in " * cite$ * warning$ }
  if$
}

FUNCTION {format.volume.number.series}
{ volume empty$
    { "" % Push the empty string as a placeholder in case everything else
         % is empty too.
      series empty$
        'skip$
        { pop$ series } % if series is not empty put in stack
      if$
      number empty$
        'skip$
        { duplicate$ empty$ % if no preceding material,
            'skip$          % do nothing, otherwise
            { ", " * }      % add a comma and space to separate.
          if$
          "\smfnumeroname" number tie.or.space.connect * % add the number information
        }
      if$
    }
%% If the volume is NOT EMPTY:
    { "vol." volume tie.or.space.connect % vol. XX
      number empty$
        { series empty$
            'skip$
            { series ", " * swap$ *}    % Series Name, vol. XX
          if$
        }
        { series empty$
            { "can't use both volume and number if series info is missing"
              warning$
              "in BibTeX entry type `" type$ * "'" * top$
            }
            { series ", " * swap$ * ", \smfnumeroname" * number tie.or.space.connect }
          if$
        }
      if$
    }
  if$
} 

FUNCTION {format.number.series}
{ volume empty$
    { number empty$
        { series field.or.null }
        { output.state mid.sentence =
            { "no." }
            { "No." }
          if$
          number tie.or.space.connect
          series empty$
            { "there's a number but no series in " cite$ * warning$ }
            { " in " * series * }
          if$
        }
      if$
    }
    { "" }
  if$
}

FUNCTION {format.edition}
{ edition empty$
    { "" }
    { output.state mid.sentence =
        { edition "l" change.case$ " \smfedition" * }
        { edition "t" change.case$ " \smfedition" * }
      if$
    }
  if$
}

INTEGERS { multiresult }

FUNCTION {multi.page.check}
{ 't :=
  #0 'multiresult :=
    { multiresult not
      t empty$ not
      and
    }
    { t #1 #1 substring$
      duplicate$ "-" =
      swap$ duplicate$ "," =
      swap$ "+" =
      or or
        { #1 'multiresult := }
        { t #2 global.max$ substring$ 't := }
      if$
    }
  while$
  multiresult
}

FUNCTION {format.pages}
{ pages empty$
    { "" }
    { pages multi.page.check
        { "\smfmultipages" pages n.dashify tie.or.space.connect }
        { "\smfunipage" pages tie.or.space.connect }
      if$
    }
  if$
}

FUNCTION {format.eid}
{ eid empty$
    { "" }
    { "art." eid tie.or.space.connect }
  if$
}

FUNCTION {format.vol.num.year}
{ volume field.or.null
  number empty$
    'skip$
    { "\penalty0 (" number * ")" * *
      volume empty$
        { "there's a number but no volume in " cite$ * warning$ }
        'skip$
      if$
    }
  if$
  year empty$
    { "year missing in" cite$ * warning$ }
    { " (" * year * ")" * }
  if$
}

FUNCTION {format.vol.num.eid}
{ volume field.or.null
  number empty$
    'skip$
    { "\penalty0 (" number * ")" * *
      volume empty$
        { "there's a number but no volume in " cite$ * warning$ }
        'skip$
      if$
    }
  if$
  year empty$
    { "year missing in" cite$ * warning$ }
    { " (" * year * ")" * }
  if$
  eid empty$
    'skip$
    { duplicate$ empty$
        { pop$ format.eid }
        { ":\penalty0 " * eid * }
      if$
    }
  if$
}

FUNCTION {format.chapter.pages}
{ chapter empty$
    'format.pages
    { type empty$
        { "chap." }
        { type "l" change.case$ }
      if$
      chapter tie.or.space.connect
      pages empty$
        'skip$
        { ", " * format.pages * }
      if$
    }
  if$
}

FUNCTION {format.in.ed.booktitle}
{ booktitle empty$
    { format.ed }
    { editor empty$
        {"\smfdansname\ " booktitle emphasize * }
        {"\smfdansname\ " format.ed * ", " *  booktitle emphasize * }
      if$
    }
  if$
}

FUNCTION {empty.misc.check}
{ author empty$ title empty$ howpublished empty$
  month empty$ year empty$ note empty$
  and and and and and
  key empty$ not and
    { "all relevant fields are empty in " cite$ * warning$ }
    'skip$
  if$
}

FUNCTION {format.thesis.type}
{ type empty$
    'skip$
    { pop$
      type "t" change.case$
    }
  if$
}

FUNCTION {format.tr.number}
{ type empty$
    { "Technical Report" }
    'type
  if$
  number empty$
    { "t" change.case$ }
    { number tie.or.space.connect }
  if$
}

%FUNCTION {format.journal.vol.number.year}
%{ journal empty$
%    { "journal name" missing.warning ""}
%    { journal emphasize }
%  if$
%  volume empty$
%    'skip$
%    { " \textup{" * volume * "}" * }
%  if$
%  number empty$
%    'skip$
%    { " (" * number * ")" * }
%  if$
%  year empty$
%    { "year" missing.warning }
%    { " (" * year * ")" * }
%  if$
%}


FUNCTION {format.article.crossref}
{ key empty$
    { journal empty$
        { "need key or journal for " cite$ * " to crossref " * crossref *
          warning$
          ""
        }
        { "\smfdansname\ \emph{" journal * "}" * }
      if$
    }
    { "\smfdansname\ " key * }
  if$
  " \citep{" * crossref * "}" *
}

FUNCTION {format.book.crossref}
{ volume empty$
    { "empty volume in " cite$ * "'s crossref of " * crossref * warning$
      "\smfdansname\ "
    }
    { "Volume" volume tie.or.space.connect
      " of " *
    }
  if$
  editor empty$
  editor field.or.null author field.or.null =
  or
    { key empty$
        { series empty$
            { "need editor, key, or series for " cite$ * " to crossref " *
              crossref * warning$
              "" *
            }
            { "\emph{" * series * "}" * }
          if$
        }
        { key * }
      if$
    }
    'skip$
  if$
  ", \citet{" * crossref * "}" *
}

FUNCTION {format.incoll.inproc.crossref}
{ editor empty$
  editor field.or.null author field.or.null =
  or
    { key empty$
        { booktitle empty$
            { "need editor, key, or booktitle for " cite$ * " to crossref " *
              crossref * warning$
              ""
            }
            { "\smfdansname\ \emph{" booktitle * "}" * }
          if$
        }
        { "\smfdansname\ " key * }
      if$
    }
    { "\smfdansname\ " }
  if$
  " \citet{" * crossref * "}" *
}

FUNCTION {write.label}
{ etiquette empty$
  { "\RHMEtiquette{" format.date "}" * * output.nonnullb
    before.all 'output.state := 
  }
  { "\RHMEtiquette{" etiquette "}" * * output.nonnullb
    before.all 'output.state := 
  }
  if$
}

FUNCTION {article}
{ output.bibitem
  "\RHMauteur{" output.nonnullb
  before.all 'output.state := 
  author empty$
    { format.editors.authors "author and editor" output.check
      editor format.key output
    }
    { format.authors output.nonnull
      crossref missing$
        { "author and editor" editor either.or.check }
        'skip$
      if$
    }
  if$
  before.all 'output.state := 
  "}" output.nonnullb
  newline$
  before.all 'output.state := 
  "\RHMfirstnewblock " output.nonnullb
  before.all 'output.state := 
  write.label
  format.title "title" output.checkb
  crossref missing$
    { journal emphasize "journal" output.check
      eid empty$
        { format.vol.num.year output%.nonnulle
          format.pages output}
        { format.vol.num.eid output }
      if$
    }
    { format.article.crossref output.nonnull
      eid empty$
        { format.pages output }
        { format.eid output }
      if$
    }
  if$
  format.issn output
  format.doi output
  format.url output
  othernote output
  note outputc
  fin.entry
}

FUNCTION {book}
{ output.bibitem
  "\RHMauteur{" output.nonnullb
  before.all 'output.state := 
  author empty$
    { format.editors.authors "author and editor" output.check
      editor format.key output
    }
    { format.authors output.nonnull
      crossref missing$
        'skip$%{ "author and editor" editor either.or.check }
        'skip$
      if$
    }
  if$
  before.all 'output.state := 
  "}" output.nonnullb
  newline$
  before.all 'output.state := 
  "\RHMfirstnewblock " output.nonnullb
  before.all 'output.state := 
  write.label
  format.btitle "title" output.checkb
  crossref missing$
    { format.editedby output
      format.volume.number.series output
      address output
      publisher "publisher" output.checkd
    }
    { new.block
      format.book.crossref output.nonnull
    }
  if$
  format.edition output
  format.date.nolabel "year" output.check
  format.isbn output
  format.doi output
  format.url output
  othernote output
  note outputc
  fin.entry
}

FUNCTION {booklet}
{ output.bibitem
  "\RHMauteur{" output.nonnullb
  before.all 'output.state := 
  format.authors output
  author format.key output
  before.all 'output.state := 
  "}" output.nonnullb
  newline$
  before.all 'output.state := 
  "\RHMfirstnewblock " output.nonnullb
  before.all 'output.state := 
  write.label
  format.title "title" output.check
  howpublished address new.block.checkb
  howpublished output
  address output
  format.date.nolabel output
  format.isbn output
  format.doi output
  format.url output
  othernote output
  note outputc
  fin.entry
}

FUNCTION {inbook}
{ output.bibitem
  "\RHMauteur{" output.nonnullb
  before.all 'output.state := 
  format.authors "author" output.check
  author format.key output
  before.all 'output.state := 
  "}" output.nonnullb
  newline$
  before.all 'output.state := 
  "\RHMfirstnewblock " output.nonnullb
  before.all 'output.state := 
  write.label
  format.title "title" output.check
  crossref missing$
    { format.in.ed.booktitle "booktitle" output.check
      format.volume.number.series output
      address output
      publisher "publisher" output.checkd
    }
    { format.chapter.pages "chapter and pages" output.check
      new.block
      format.incoll.inproc.crossref output.nonnull
    }
  if$
  format.edition output
  format.date.nolabel "year" output.check
  format.chapter.pages "chapter and pages" output.check
  format.isbn output
  format.doi output
  format.url output
  othernote output
  note outputc
  fin.entry
}

FUNCTION {incollection}
{ output.bibitem
  "\RHMauteur{" output.nonnullb
  before.all 'output.state := 
  format.authors "author" output.check
  author format.key output
  before.all 'output.state := 
  "}" output.nonnullb
  newline$
  before.all 'output.state := 
  "\RHMfirstnewblock " output.nonnullb
  before.all 'output.state := 
  write.label
  format.title "title" output.check
  crossref missing$
    { format.in.ed.booktitle "booktitle" output.check
      format.volume.number.series output
      address output
      publisher "publisher" output.checkd
      format.edition output
      format.date.nolabel "year" output.check
      format.pages output
    }
    { format.incoll.inproc.crossref output.nonnull
      format.pages output
    }
  if$
  format.isbn output
  format.doi output
  format.url output
  othernote output
  note outputc
  fin.entry
}

FUNCTION {inproceedings}
{ output.bibitem
  "\RHMauteur{" output.nonnullb
  before.all 'output.state := 
  format.authors "author" output.check
  author format.key output
  before.all 'output.state := 
  "}" output.nonnullb
  newline$
  before.all 'output.state := 
  "\RHMfirstnewblock " output.nonnullb
  before.all 'output.state := 
  write.label
  format.title "title" output.check
  crossref missing$
    { format.in.ed.booktitle "booktitle" output.check
      format.volume.number.series output
      format.pages output
      address empty$
        { organization publisher new.sentence.checkb
          organization output
          publisher output
          format.date.nolabel "year" output.check
        }
        { address output.nonnull
          format.date.nolabel "year" output.check
          new.sentence
          organization output
          publisher output
        }
      if$
    }
    { format.incoll.inproc.crossref output.nonnull
      format.pages output
    }
  if$
  format.isbn output
  format.doi output
  format.url output
  othernote output
  note outputc
  fin.entry
}

FUNCTION {conference} { inproceedings }

FUNCTION {manual}
{ output.bibitem
  "\RHMauteur{" output.nonnullb
  before.all 'output.state := 
  format.authors output
  author format.key output
  before.all 'output.state := 
  "}" output.nonnullb
  newline$
  before.all 'output.state := 
  "\RHMfirstnewblock " output.nonnullb
  before.all 'output.state := 
  write.label
  format.btitle "title" output.check
  organization address new.block.checkb
  organization output
  address output
  format.edition output
  format.date.nolabel output
  format.url output
  othernote output
  note outputc
  fin.entry
}

FUNCTION {mastersthesis}
{ output.bibitem
  "\RHMauteur{" output.nonnullb
  before.all 'output.state := 
  format.authors "author" output.check
  author format.key output
  before.all 'output.state := 
  "}" output.nonnullb
  newline$
  before.all 'output.state := 
  "\RHMfirstnewblock " output.nonnullb
  before.all 'output.state := 
  write.label
  format.title "title" output.check
  "Master's thesis" format.thesis.type output.nonnull
  school "school" output.check
  address output
  format.date.nolabel "year" output.check
  format.url output
  othernote output
  note outputc
  fin.entry
}

FUNCTION {misc}
{ output.bibitem
  "\RHMauteur{" output.nonnullb
  before.all 'output.state := 
  format.authors output
  author format.key output
  before.all 'output.state := 
  "}" output.nonnullb
  newline$
  before.all 'output.state := 
  "\RHMfirstnewblock " output.nonnullb
  before.all 'output.state := 
  write.label
  title howpublished new.block.checkb
  format.title output
  howpublished new.block.checka
  howpublished output
  format.date.nolabel output
  format.issn output
  format.url output
  othernote output
  note outputc
  fin.entry
  empty.misc.check
}

FUNCTION {phdthesis}
{ output.bibitem
  "\RHMauteur{" output.nonnullb
  before.all 'output.state := 
  format.authors "author" output.check
  author format.key output
  before.all 'output.state := 
  "}" output.nonnullb
  newline$
  before.all 'output.state := 
  "\RHMfirstnewblock " output.nonnullb
  before.all 'output.state := 
  write.label
  format.btitle "title" output.check
  "\smfphdthesisname" format.thesis.type output.nonnull
  school "school" output.check
  address output
  format.date.nolabel "year" output.check
  format.url output
  othernote output
  note outputc
  fin.entry
}

FUNCTION {proceedings}
{ output.bibitem
  "\RHMauteur{" output.nonnullb
  before.all 'output.state := 
  format.editors.authors output
  editor format.key output
  before.all 'output.state := 
  "}" output.nonnullb
  newline$
  before.all 'output.state := 
  "\RHMfirstnewblock " output.nonnullb
  before.all 'output.state := 
  write.label
  format.btitle "title" output.check
  format.volume.number.series output
  organization output
  address output
  publisher "publisher" output.checkd
  format.date.nolabel "year" output.check
  format.isbn output
  format.doi output
  format.url output
  othernote output
  note outputc
  fin.entry
}

FUNCTION {techreport}
{ output.bibitem
  "\RHMauteur{" output.nonnullb
  before.all 'output.state := 
  format.authors "author" output.check
  author format.key output
  before.all 'output.state := 
  "}" output.nonnullb
  newline$
  before.all 'output.state := 
  "\RHMfirstnewblock " output.nonnullb
  before.all 'output.state := 
  write.label
  format.title "title" output.check
  new.block
  format.tr.number output.nonnull
  institution "institution" output.check
  address output
  format.date.nolabel "year" output.check
  format.url output
  othernote output
  note outputc
  fin.entry
}

FUNCTION {unpublished}
{ output.bibitem
  "\RHMauteur{" output.nonnullb
  before.all 'output.state := 
  format.authors "author" output.check
  author format.key output
  before.all 'output.state := 
  "}" output.nonnullb
  newline$
  before.all 'output.state := 
  "\RHMfirstnewblock " output.nonnullb
  before.all 'output.state := 
  write.label
  format.title "title" output.check
  format.url output
  othernote "othernote" output.check
  format.date.nolabel output
  note outputc
  fin.entry
}

FUNCTION {default.type} { misc }


READ

FUNCTION {sortify}
{ purify$
  "l" change.case$
}

INTEGERS { len }

FUNCTION {chop.word}
{ 's :=
  'len :=
  s #1 len substring$ =
    { s len #1 + global.max$ substring$ }
    's
  if$
}

FUNCTION {format.lab.names}
{ 's :=
  s #1 "{vv~}{ll}" format.name$
  s num.names$ duplicate$
  #2 >
    { pop$ " et~al." * }
    { #2 <
        'skip$
        { s #2 "{ff }{vv }{ll}{ jj}" format.name$ "others" =
            { " et~al." * }
            { " \smfandname\ " * s #2 "{vv~}{ll}" format.name$ * }
          if$
        }
      if$
    }
  if$
}

FUNCTION {author.key.label}
{ author empty$
    { key empty$
        { cite$ #1 #3 substring$ }
        'key
      if$
    }
    { author format.lab.names }
  if$
}

FUNCTION {author.editor.key.label}
{ author empty$
    { editor empty$
        { key empty$
            { cite$ #1 #3 substring$ }
            'key
          if$
        }
        { editor format.lab.names }
      if$
    }
    { author format.lab.names }
  if$
}

FUNCTION {author.key.organization.label}
{ author empty$
    { key empty$
        { organization empty$
            { cite$ #1 #3 substring$ }
            { "The " #4 organization chop.word #3 text.prefix$ }
          if$
        }
        'key
      if$
    }
    { author format.lab.names }
  if$
}

FUNCTION {editor.key.organization.label}
{ editor empty$
    { key empty$
        { organization empty$
            { cite$ #1 #3 substring$ }
            { "The " #4 organization chop.word #3 text.prefix$ }
          if$
        }
        'key
      if$
    }
    { editor format.lab.names }
  if$
}

FUNCTION {calc.short.authors}
{ type$ "book" =
  type$ "inbook" =
  or
  type$ "article" =
  or
    'author.editor.key.label
    { type$ "proceedings" =
        'editor.key.organization.label
        { type$ "manual" =
            'author.key.organization.label
            'author.key.label
          if$
        }
      if$
    }
  if$
  'short.list :=
}

FUNCTION {calc.label}
{ calc.short.authors
  short.list
  "("
  *
  year duplicate$ empty$
  short.list key field.or.null = or
     { pop$ "" }
     'skip$
  if$
  *
  'label :=
}

FUNCTION {sort.format.names}
{ 's :=
  #1 'nameptr :=
  ""
  s num.names$ 'numnames :=
  numnames 'namesleft :=
    { namesleft #0 > }
    { nameptr #1 >
        { "   " * }
        'skip$
      if$
      s nameptr "{vv{ } }{ll{ }}{  ff{ }}{  jj{ }}" format.name$ 't :=
      nameptr numnames = t "others" = and
        { "et al" * }
        { t sortify * }
      if$
      nameptr #1 + 'nameptr :=
      namesleft #1 - 'namesleft :=
    }
  while$
}

FUNCTION {sort.format.title}
{ 't :=
  "A " #2
    "An " #3
      "The " #4 t chop.word
    chop.word
  chop.word
  sortify
  #1 global.max$ substring$
}

FUNCTION {author.sort}
{ author empty$
    { key empty$
        { "to sort, need author or key in " cite$ * warning$
          ""
        }
        { key sortify }
      if$
    }
    { author sort.format.names }
  if$
}

FUNCTION {author.editor.sort}
{ author empty$
    { editor empty$
        { key empty$
            { "to sort, need author, editor, or key in " cite$ * warning$
              ""
            }
            { key sortify }
          if$
        }
        { editor sort.format.names }
      if$
    }
    { author sort.format.names }
  if$
}

FUNCTION {author.organization.sort}
{ author empty$
    { organization empty$
        { key empty$
            { "to sort, need author, organization, or key in " cite$ * warning$
              ""
            }
            { key sortify }
          if$
        }
        { "The " #4 organization chop.word sortify }
      if$
    }
    { author sort.format.names }
  if$
}

FUNCTION {editor.organization.sort}
{ editor empty$
    { organization empty$
        { key empty$
            { "to sort, need editor, organization, or key in " cite$ * warning$
              ""
            }
            { key sortify }
          if$
        }
        { "The " #4 organization chop.word sortify }
      if$
    }
    { editor sort.format.names }
  if$
}

INTEGERS { seq.num }

FUNCTION {init.seq}
{ #0 'seq.num :=}

EXECUTE {init.seq}

FUNCTION {int.to.fix}
{ "000000000" swap$ int.to.str$ *
  #-1 #10 substring$
}

FUNCTION {presort}
{ calc.label
  label sortify
  "    "
  *
  seq.num #1 + 'seq.num :=
  seq.num  int.to.fix
  'sort.label :=
  sort.label *
  #1 entry.max$ substring$
  'sort.key$ :=
}

ITERATE {presort}

SORT

STRINGS { longest.label last.label next.extra }

INTEGERS { longest.label.width last.extra.num number.label }

FUNCTION {initialize.longest.label}
{ "" 'longest.label :=
  #0 int.to.chr$ 'last.label :=
  "" 'next.extra :=
  #0 'longest.label.width :=
  #0 'last.extra.num :=
  #0 'number.label :=
}

FUNCTION {forward.pass}
{ last.label label =
    { last.extra.num #1 + 'last.extra.num :=
      last.extra.num int.to.chr$ 'extra.label :=
    }
    { "a" chr.to.int$ 'last.extra.num :=
      "" 'extra.label :=
      label 'last.label :=
    }
  if$
  number.label #1 + 'number.label :=
}

FUNCTION {reverse.pass}
{ next.extra "b" =
    { "a" 'extra.label := }
    'skip$
  if$
  extra.label 'next.extra :=
  extra.label
  duplicate$ empty$
    'skip$
    { "{\natexlab{" swap$ * "}}" * }
  if$
  'extra.label :=
  label extra.label * 'label :=
}

EXECUTE {initialize.longest.label}

ITERATE {forward.pass}

REVERSE {reverse.pass}

FUNCTION {bib.sort.order}
{ sort.label  'sort.key$ :=
}

ITERATE {bib.sort.order}

SORT

FUNCTION {begin.bib}
{   preamble$ empty$
    'skip$
    { preamble$ write$ newline$ }
  if$
  "\begin{thebibliography}{" number.label int.to.str$ * "}" *
  write$ newline$
  "\providecommand{\natexlab}[1]{#1}"
  write$ newline$
  "\providecommand{\url}[1]{\texttt{#1}}"
  write$ newline$
  "\expandafter\ifx\csname urlstyle\endcsname\relax"
  write$ newline$
  "  \providecommand{\doi}[1]{doi: #1}\else"
  write$ newline$
  "  \providecommand{\doi}{doi: \begingroup \urlstyle{rm}\Url}\fi"
  write$ newline$
  "\renewcommand{\newblock}{}"
  write$ newline$
}

EXECUTE {begin.bib}

EXECUTE {init.state.consts}

ITERATE {call.type$}

FUNCTION {end.bib}
{ newline$
  "\end{thebibliography}" write$ newline$
}

EXECUTE {end.bib}
