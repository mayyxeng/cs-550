TARGETS := template.pdf

.PHONY: $(TARGETS) default clean show

default: $(TARGETS)

$(TARGETS):
	(latexmk -pdf -pdflatex="pdflatex -interaction=nonstopmode -synctex=1" -use-make $(@:.pdf=.tex) \
	  3>&2 2>&1 1>&3 | sed -e 's/\(^.*undefined.*$$\)/$(@:.pdf=.tex):0 warning: \1/') 3>&2 2>&1 1>&3

%.pdf: %.eps
	epstopdf --outfile $@ $<

%.pdf: %.odp
	if which libreoffice 2>&1 >/dev/null; then \
		cd $(dir $<); \
		libreoffice --headless --convert-to pdf $(notdir $<); \
	else \
		if [ -f $@ ]; then \
			touch $@; \
		fi \
	fi

%.eps: %.pdf
	pdftops -eps $< $@

clean:
	latexmk -C
	rm -f *.xcp

show: $(TARGETS)
	xdg-open $<