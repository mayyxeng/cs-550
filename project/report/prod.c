assume in = $\hat{\texttt{in}}$;
assume out = $\hat{\texttt{out}}$;
assume len = $\hat{\texttt{len}}$;
assume sub_len = $\hat{\texttt{sub\_len}}$;
i = 0; $\hat{\texttt{i}}$ = 0; j = 0; $\hat{\texttt{j}}$ = 0;
assert (i < len) = ($\hat{\texttt{i}}$ < $\hat{\texttt{len}}$); // trivial
while (i < len) do:
    assert ((i $\geq$ l_idx) && (i < l_idx + sub_len)) = (($\hat{\texttt{i}}$ $\geq$ _l_idx) && ($\hat{\texttt{i}}$ < _l_idx + $\hat{\texttt{sub\_len}}$) // fails;
    if ((i $\geq$ l_idx) && (i < l_idx + sub_len)) then
        assert i = $\hat{\texttt{i}}$ && j = $\hat{\texttt{j}}$; // trivial
        out[j] = in[i]; $\hat{\texttt{out}}$[$\hat{\texttt{j}}$] = $\hat{\texttt{in}}$[_i];
        j = j + 1; $\hat{\texttt{j}}$ = $\hat{\texttt{j}}$ + 1;
    i = i + 1; $\hat{\texttt{i}}$ = $\hat{\texttt{i}}$ + 1;