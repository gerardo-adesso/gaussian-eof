import re,glob,subprocess,os
R='/home/claude/gaussian-eof'
files={os.path.basename(f)[:-5]:open(f).read().split('\n') for f in glob.glob(R+'/Thm2Cert/*.lean')}
TR={'ℹ':'i','𝖠':'A','𝖡':'B','𝖢':'C','𝖥':'F','𝒢':'G','𝓔':'E'}
def tr(s):
    for k,v in TR.items(): s=s.replace(k,v)
    return s
def grab(name):
    for fn,L in files.items():
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
groups=[
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
scope=readme[readme.index('## Inputs'):].split('\n',1)[1].strip()
out=[r'''\documentclass[10pt,a4paper]{article}
\usepackage[margin=2cm]{geometry}
\usepackage{fontspec}
\setmainfont{DejaVu Serif}\setmonofont[Scale=0.82]{DejaVu Sans Mono}
\usepackage{amsmath,amssymb}\usepackage{fvextra,xcolor,hyperref,titlesec}
\hypersetup{colorlinks,urlcolor=blue!50!black,linkcolor=black}
\definecolor{bg}{gray}{0.96}
\fvset{fontsize=\small,frame=single,framesep=2mm,rulecolor=\color{gray!50}}
\titleformat{\section}{\large\bfseries}{\thesection}{1em}{}
\begin{document}
\begin{center}
{\LARGE\bfseries Machine-checked certificate}\\[4pt]
{\large Theorem 2 of G.~Adesso, \emph{Optimality of Gaussian entanglement of formation}}\\[2pt]
\href{https://arxiv.org/abs/2608.01909v3}{arXiv:2608.01909v3}\\[8pt]
Lean 4 (v4.35.0-rc4) + Mathlib (commit \texttt{49fd9de}) \quad$\cdot$\quad
\href{https://github.com/gerardo-adesso/gaussian-eof}{github.com/gerardo-adesso/gaussian-eof} @ \texttt{'''+commit[:7]+r'''}\\[2pt]
9 October 2026
\end{center}
\section*{Summary}
All statements below are proved in Lean~4 against Mathlib, with no \texttt{sorry}, \texttt{admit} or additional axioms. The kernel reports that each depends only on \texttt{propext}, \texttt{Classical.choice} and \texttt{Quot.sound} (Sec.~\ref{sec:ver}). They comprise Lemma~S5 in full (positivity, kernel, and $M(x)\geq\gamma K(x)$ with the explicit constant $\gamma=\kappa\sinh w-w\coth w-|\alpha-\beta|/2$); the derivation of Eqs.~(S:defects) and (S:Q12) from the Euler equation in the Schmidt-basis matrix model; the identity (S:mainid); the rigidity statement; and the scalar reduction from the minimum principle to Theorem~2. Statements are printed verbatim from the source; the full source is in the Appendix.
\section*{Not formalized (inputs)}
\begin{itemize}''']
out.append(r"""\item Operator facts on Fock space: the canonical commutation relations, which give the commutators $[T,O]$, the sum rules (S:wccr), and the matrix model with finitely many relevant directions; the TMSV moments and the identity $\lambda\hat D_t=T+\lambda$.
\item The second-variation formula $Q(Y)=\mathrm{Re}\langle Y,(T-\mu-\mathsf F)Y\rangle$ (Daleckii--Krein), the Euler equation (S:euler) and the stability inequality (S:stability).
\item The vacuum/gap statement (S:gap): the joint vacuum of the canonical annihilators $f_j,e_j$ is $\bigotimes_j\Psi_{q_j}$.
\item The infinite-dimensional analysis: infinite Schmidt rank, Lemma~S6, regularization, existence of minimizers.
\end{itemize}
These require operator theory on infinite-dimensional Hilbert spaces (unbounded ladder operators, trace-class operators, von Neumann entropy) not yet available in Mathlib. Comments in the printed source use plain letters in place of a few script glyphs ($\mathcal E$, $\mathcal G$, $\mathsf A,\mathsf B,\mathsf C,\mathsf F$).""")
for title,names in groups:
    out.append(r'\section{'+title+'}')
    for n in names:
        fn,txt=grab(n)
        out.append(r'\noindent\texttt{'+esc(n)+r'} \hfill {\footnotesize\texttt{Thm2Cert/'+fn+r'.lean}}')
        out.append(r'\begin{Verbatim}[breaklines]'+'\n'+tr(txt)+'\n'+r'\end{Verbatim}')
out.append(r'\section{Verification record}\label{sec:ver}')
out.append(r'\begin{Verbatim}[fontsize=\scriptsize]'+'\n'+ver.strip()+'\n'+r'\end{Verbatim}')
out.append(r'\clearpage\appendix\section*{Appendix: full source}')
for fn in ['MatrixLemma','Identity','Reduction','Comparison','Derivation']:
    out.append(r'\subsection*{Thm2Cert/'+fn+'.lean}')
    out.append(r'\begin{Verbatim}[fontsize=\scriptsize,numbers=left,numbersep=3pt,frame=none]'+'\n'+tr('\n'.join(files[fn]).rstrip())+'\n'+r'\end{Verbatim}')
out.append(r'\end{document}')
open('certificate.tex','w').write('\n'.join(out))
