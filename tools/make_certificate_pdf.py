import re,glob,subprocess,os
R='/home/claude/gaussian-eof'
FILES={D:{os.path.basename(f)[:-5]:open(f).read().split('\n') for f in glob.glob(R+'/'+D+'/*.lean')} for D in ['Thm1Cert','Thm2Cert']}
TR={'ℹ':'i'}
def tr(s):
    for k,v in TR.items(): s=s.replace(k,v)
    return s
def grab(name,D):
    for fn,L in FILES[D].items():
        for i,l in enumerate(L):
            if re.match(r'^(theorem|lemma|def|structure)\s+'+re.escape(name)+r'(\s|$)',l):
                j=i
                if i>0 and L[i-1].rstrip().endswith('-/'):
                    j=i-1
                    while not L[j].lstrip().startswith('/--'): j-=1
                if L[i].startswith(('def','structure')):
                    k=i
                    while k+1<len(L) and L[k+1].strip()!='': k+=1
                    out=L[j:k+1]
                else:
                    k=i
                    while ':= by' not in L[k] and not L[k].rstrip().endswith(':='): k+=1
                    out=L[j:k+1]; out[-1]=out[-1].replace(':= by','').rstrip()
                    if out[-1].endswith(':='): out[-1]=out[-1][:-2].rstrip()
                return fn,'\n'.join(out)
    raise Exception(name)
groups1=[
 ("Definitions",["pos","dd","dlt","alpha","beta","wt","mass","pre","en","Hs","Ft","zs","phi","nbar","Tz","Ups","BRKUpsilon","BRK"]),
 ("Theorem S1: singular-value defect inequality",["drop_lemma","pointwise","defect_inequality","defect_inequality_tsum"]),
 ("Theorem S2: geometric isotonic compression",["pool_step","pava_exists","entropy_le_of_prefix","compression"]),
 ("Thermal closure",["H_thermal","F_thermal","support","Fmoments","Ups_eq","brk_of_upsilon"]),
 ("Theorem 1 and corollaries",["thm1_spectrum","theorem1","theorem1_upsilon","theorem1_limit","entropy_truncation","theorem1_endpoint","theorem1_endpoint_state","fixed_entanglement","fixed_entanglement_endpoint","separability_criterion"]),
]
groups2=[
 ("Definitions",["f","b","Mdiag","Moff","Hyp","QM","Kdiag","QK","gam","Lker","Fdk","kk","sfA","sfC","Q1","Q2","O1v","O2v","kterm","term","lam","dt","gfun","EE"]),
 ("Lemma S5: positivity and kernel",["hyp_nonvacuous","lemmaS5_psd","lemmaS5_pd","lemmaS5_kernel","lemmaS5_null","lemmaS5_complex","lemmaS5_complex_pd","lemmaS5_complex_kernel"]),
 ("Lemma S5: comparison with explicit constant",["gam_pos","lemmaS5_gamma","lemmaS5_gamma_complex"]),
 ("Eqs. (S:defects), (S:Q12), (S:mainid)",["defects","Q1_from_euler","Q2_from_euler","mainid","mainid_general"]),
 ("Rigidity",["rigidity","rigidity_multi","stationary_rigidity"]),
 ("Reduction to Theorem 2",["calib_iff","lam_pos","hyp_of_lam","tmsv_value","energy_identity","thm2_of_minprinciple"]),
]
def esc(s): return s.replace('\\','\\textbackslash{}').replace('_','\\_').replace('&','\\&').replace('#','\\#').replace('%','\\%')
commit=subprocess.check_output(['git','-C',R,'rev-parse','HEAD']).decode().strip()
ver=tr(open(R+'/VERIFICATION.txt').read())
readme=open(R+'/README.md').read()
out=[r'''\documentclass[10pt,a4paper]{article}
\usepackage[margin=2cm]{geometry}
\usepackage{fontspec}
\setmainfont{DejaVu Serif}\setmonofont[Scale=0.82]{DejaVu Sans Mono}
\usepackage{amsmath,amssymb}\usepackage{fvextra,xcolor,hyperref,titlesec}
\hypersetup{colorlinks,urlcolor=blue!50!black,linkcolor=black}
\definecolor{bg}{gray}{0.96}
\fvset{fontsize=\small,frame=single,framesep=2mm,rulecolor=\color{gray!50}}
\titleformat{\section}{\large\bfseries}{\thesection}{1em}{}
\newfontfamily\fbfont{DejaVu Math TeX Gyre}[Scale=0.82]
\XeTeXinterchartokenstate=1
\newXeTeXintercharclass\fbclass
\XeTeXcharclass"2113=\fbclass
\XeTeXcharclass"1D4A2=\fbclass
\XeTeXcharclass"1D4D4=\fbclass
\XeTeXcharclass"1D4D5=\fbclass
\XeTeXcharclass"1D4DD=\fbclass
\XeTeXcharclass"1D5A0=\fbclass
\XeTeXcharclass"1D5A1=\fbclass
\XeTeXcharclass"1D5A2=\fbclass
\XeTeXcharclass"1D5A5=\fbclass
\XeTeXinterchartoks 0 \fbclass = {\begingroup\fbfont}
\XeTeXinterchartoks 4095 \fbclass = {\begingroup\fbfont}
\XeTeXinterchartoks \fbclass 0 = {\endgroup}
\XeTeXinterchartoks \fbclass 4095 = {\endgroup}

\begin{document}
\begin{center}
{\LARGE\bfseries Machine-checked certificate}\\[4pt]
{\large Theorems 1 and 2 of G.~Adesso, \emph{Optimality of Gaussian entanglement of formation}}\\[2pt]
\href{https://arxiv.org/abs/2608.01909v3}{arXiv:2608.01909v3}\\[8pt]
Lean 4 (v4.35.0-rc4) + Mathlib (commit \texttt{49fd9de}) \quad$\cdot$\quad
\href{https://github.com/gerardo-adesso/gaussian-eof}{github.com/gerardo-adesso/gaussian-eof} @ \texttt{'''+commit[:7]+r'''}\\[2pt]
9 October 2026
\end{center}
\section*{Summary}
All statements below are proved in Lean~4 against Mathlib, with no \texttt{sorry}, \texttt{admit} or additional axioms; the kernel reports that each depends only on \texttt{propext}, \texttt{Classical.choice} and \texttt{Quot.sound} (Sec.~\ref{sec:ver}). Statements are printed verbatim from the source; the full source is in the Appendix.

\textbf{Theorem 1} (Part I): the singular-value defect inequality (Theorem~S1) in the Schmidt-basis matrix model; the geometric isotonic compression (Theorem~S2), including the pool-adjacent-violators construction and Schur concavity; the thermal closure (S:thermalF, S:support, S:Fmoments, S:UpsilonF); the assembly $E(\psi)+\lambda_{q,t}[D_t(\psi)-d_t(q)]\geq\mathcal E(q)$ for finite and infinite Schmidt rank; the endpoint $q=t$ and Eq.~(S:fixedE) for $0\leq q\leq t$.

\textbf{Theorem 2} (Part II): Lemma~S5 in full (positivity, kernel, and $M(x)\geq\gamma K(x)$ with the explicit constant $\gamma=\kappa\sinh w-w\coth w-|\alpha-\beta|/2$); the derivation of Eqs.~(S:defects) and (S:Q12) from the Euler equation; the identity (S:mainid); rigidity; the scalar reduction from the minimum principle to Theorem~2.
\section*{Not formalized (inputs)}
\textbf{Theorem 1.}
\begin{itemize}
\item The meta log-Sobolev theorem of Beigi and Rahimi-Keshari, used only for diagonal states of finite rank (\texttt{BRKUpsilon}), together with the diagonal-state moments $\mathrm{Tr}(\rho_z a^\dagger a)=\bar n$, $\mathrm{Tr}(\sqrt{\rho_z}a\sqrt{\rho_z}a^\dagger)=T_z$.
\item Fock-space facts: $E(\psi)=H(c^2)$, $D_t=G_t+1-t^2$, the matrix model $X=U^\dagger aU$, $Y=V^\dagger aV$ in Schmidt bases indexed by $\mathbb N$ (available for every finite-rank state), the index identities from $[a,a^\dagger]=1$, and, for general infinite-rank states, the convergence $G_t(C^{(L)})\to G_t(C)$ of normalized Schmidt truncations (then \texttt{theorem1\_limit} applies).
\end{itemize}
\textbf{Theorem 2.}
\begin{itemize}
\item Operator facts on Fock space: the canonical commutation relations (giving $[T,O]$, the sum rules (S:wccr) and the matrix model with finitely many relevant directions); the TMSV moments and $\lambda\hat D_t=T+\lambda$.
\item The second-variation formula $Q(Y)=\mathrm{Re}\langle Y,(T-\mu-\mathsf F)Y\rangle$ (Daleckii--Krein), the Euler equation (S:euler) and the stability inequality (S:stability).
\item The vacuum/gap statement (S:gap): the joint vacuum of the canonical annihilators $f_j,e_j$ is $\bigotimes_j\Psi_{q_j}$.
\item The infinite-dimensional analysis: infinite Schmidt rank, Lemma~S6, regularization, existence of minimizers.
\end{itemize}
These require operator theory on infinite-dimensional Hilbert spaces (unbounded ladder operators, trace-class operators, von Neumann entropy) not yet available in Mathlib.
''']
for part,D,groups in [("Part I: Theorem 1","Thm1Cert",groups1),("Part II: Theorem 2","Thm2Cert",groups2)]:
    out.append(r'\clearpage\part*{'+part+'}')
    for title,names in groups:
        out.append(r'\section{'+title+'}')
        for n in names:
            fn,txt=grab(n,D)
            out.append(r'\noindent\texttt{'+esc(n)+r'} \hfill {\footnotesize\texttt{'+D+'/'+fn+r'.lean}}')
            out.append(r'\begin{Verbatim}[breaklines]'+'\n'+tr(txt)+'\n'+r'\end{Verbatim}')
out.append(r'\section{Verification record}\label{sec:ver}')
out.append(r'\begin{Verbatim}[fontsize=\scriptsize]'+'\n'+ver.strip()+'\n'+r'\end{Verbatim}')
out.append(r'\clearpage\appendix\section*{Appendix: full source}')
for D,fns in [("Thm1Cert",['Defect','Compression','Closure','Assembly','Upsilon','Corollaries']),("Thm2Cert",['MatrixLemma','Identity','Reduction','Comparison','Derivation'])]:
    for fn in fns:
        out.append(r'\subsection*{'+D+'/'+fn+'.lean}')
        out.append(r'\begin{Verbatim}[fontsize=\scriptsize,numbers=left,numbersep=3pt,frame=none]'+'\n'+tr('\n'.join(FILES[D][fn]).rstrip())+'\n'+r'\end{Verbatim}')
out.append(r'\end{document}')
open('certificate.tex','w').write('\n'.join(out))
