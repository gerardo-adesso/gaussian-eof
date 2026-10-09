import re,glob,subprocess,os,sys,shutil,tempfile
R=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
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
VER=tr(open(R+'/VERIFICATION.txt').read()).split('\n')
PREAMBLE=r"""\documentclass[10pt,a4paper]{article}
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

"""

SUMMARY={1:r"""\textbf{Certified:} the singular-value defect inequality (Theorem~S1) in the Schmidt-basis matrix model; the geometric isotonic compression (Theorem~S2), including the pool-adjacent-violators construction and Schur concavity of the entropy; the thermal closure (S:thermalF, S:support, S:Fmoments, S:UpsilonF); the assembly $E(\psi)+\lambda_{q,t}[D_t(\psi)-d_t(q)]\geq\mathcal E(q)$ for finite and infinite Schmidt rank; the endpoint $q=t$ and Eq.~(S:fixedE) for $0\leq q\leq t$. The definitions of $\mathcal E$, $\lambda_{q,t}$, $d_t$ (\texttt{Thm2Cert/Reduction.lean}) and the $2\times2$ lemma \texttt{quad\_nonneg} (\texttt{Thm2Cert/MatrixLemma.lean}) are shared with the Theorem~2 certificate.
\section*{Not formalized (inputs)}
\begin{itemize}
\item The meta log-Sobolev theorem of Beigi and Rahimi-Keshari, used only for diagonal states of finite rank (\texttt{BRKUpsilon}), with the diagonal-state moments $\mathrm{Tr}(\rho_z a^\dagger a)=\bar n$, $\mathrm{Tr}(\sqrt{\rho_z}a\sqrt{\rho_z}a^\dagger)=T_z$.
\item Fock-space facts: $E(\psi)=H(c^2)$, $D_t=G_t+1-t^2$, the matrix model $X=U^\dagger aU$, $Y=V^\dagger aV$ in Schmidt bases indexed by $\mathbb N$ (available for every finite-rank state), the index identities from $[a,a^\dagger]=1$, and, for general infinite-rank states, the convergence $G_t(C^{(L)})\to G_t(C)$ of normalized Schmidt truncations (then \texttt{theorem1\_limit} applies).
\end{itemize}""",
2:r"""\textbf{Certified:} Lemma~S5 in full (positivity, kernel, and $M(x)\geq\gamma K(x)$ with the explicit constant $\gamma=\kappa\sinh w-w\coth w-|\alpha-\beta|/2$); the derivation of Eqs.~(S:defects) and (S:Q12) from the Euler equation in the Schmidt-basis matrix model; the identity (S:mainid); rigidity; the scalar reduction from the minimum principle to Theorem~2.
\section*{Not formalized (inputs)}
\begin{itemize}
\item Operator facts on Fock space: the canonical commutation relations (giving $[T,O]$, the sum rules (S:wccr) and the matrix model with finitely many relevant directions); the TMSV moments and $\lambda\hat D_t=T+\lambda$.
\item The second-variation formula $Q(Y)=\mathrm{Re}\langle Y,(T-\mu-\mathsf F)Y\rangle$ (Daleckii--Krein), the Euler equation (S:euler) and the stability inequality (S:stability).
\item The vacuum/gap statement (S:gap): the joint vacuum of the canonical annihilators $f_j,e_j$ is $\bigotimes_j\Psi_{q_j}$.
\item The infinite-dimensional analysis: infinite Schmidt rank, Lemma~S6, regularization, existence of minimizers.
\end{itemize}
These require operator theory on infinite-dimensional Hilbert spaces (unbounded ladder operators, trace-class operators, von Neumann entropy) not yet available in Mathlib."""}
SHARED1=[("Shared definitions (Thm2Cert)",["lam","dt","gfun","EE","quad_nonneg"])]
FNS={1:['Defect','Compression','Closure','Assembly','Upsilon','Corollaries'],
     2:['MatrixLemma','Identity','Reduction','Comparison','Derivation']}

def verification(k):
    D='Thm%dCert'%k
    lines=[]; sec=None
    for l in VER:
        if l.startswith('=='): sec=l; lines.append(l); continue
        if sec is None or 'Clean build' in (sec or ''):
            if sec is None or not ('Cert.' in l or 'Cert (' in l) or D in l or ('Thm2Cert.MatrixLemma' in l or 'Thm2Cert.Reduction' in l) and k==1:
                lines.append(l)
        elif 'Axiom' in sec:
            if l.startswith("'") and not l.startswith("'"+D): continue
            lines.append(l)
        elif 'SHA' in sec:
            if l.strip() and not (D in l or 'lakefile' in l or 'lean-toolchain' in l or 'Certificate.lean' in l
                                  or (k==1 and ('Thm2Cert/Reduction' in l or 'Thm2Cert/MatrixLemma' in l))):
                continue
            lines.append(l)
        else:
            lines.append(l)
    return '\n'.join(lines).strip()

def build(k):
    D='Thm%dCert'%k
    groups=(SHARED1+groups1) if k==1 else groups2
    out=[PREAMBLE+r"""\begin{document}
\begin{center}
{\LARGE\bfseries Machine-checked certificate: Theorem~%d}\\[4pt]
{\large G.~Adesso, \emph{Optimality of Gaussian entanglement of formation}}\\[2pt]
\href{https://arxiv.org/abs/2608.01909v3}{arXiv:2608.01909v3}\\[8pt]
Lean 4 (v4.35.0-rc4) + Mathlib (commit \texttt{49fd9de}) \quad$\cdot$\quad
\href{https://github.com/gerardo-adesso/gaussian-eof}{github.com/gerardo-adesso/gaussian-eof} @ \texttt{%s}\\[2pt]
9 October 2026
\end{center}
\section*{Summary}
All statements below are proved in Lean~4 against Mathlib, with no \texttt{sorry}, \texttt{admit} or additional axioms; the kernel reports that each depends only on \texttt{propext}, \texttt{Classical.choice} and \texttt{Quot.sound} (Sec.~\ref{sec:ver}). Statements are printed verbatim from the source; the full source is in the Appendix.

"""%(k,commit[:7])+SUMMARY[k]]
    for title,names in groups:
        out.append(r'\section{'+title+'}')
        for n in names:
            src = 'Thm2Cert' if title.startswith('Shared') else D
            fn,txt=grab(n,src)
            out.append(r'\noindent\texttt{'+esc(n)+r'} \hfill {\footnotesize\texttt{'+src+'/'+fn+r'.lean}}')
            out.append(r'\begin{Verbatim}[breaklines]'+'\n'+tr(txt)+'\n'+r'\end{Verbatim}')
    out.append(r'\section{Verification record}\label{sec:ver}')
    out.append(r'\begin{Verbatim}[fontsize=\scriptsize]'+'\n'+verification(k)+'\n'+r'\end{Verbatim}')
    out.append(r'\clearpage\appendix\section*{Appendix: full source}')
    for fn in FNS[k]:
        out.append(r'\subsection*{'+D+'/'+fn+'.lean}')
        out.append(r'\begin{Verbatim}[fontsize=\scriptsize,numbers=left,numbersep=3pt,frame=none]'+'\n'+tr('\n'.join(FILES[D][fn]).rstrip())+'\n'+r'\end{Verbatim}')
    out.append(r'\end{document}')
    tmp=tempfile.mkdtemp()
    open(tmp+'/c.tex','w').write('\n'.join(out))
    for _ in range(2):
        subprocess.run(['xelatex','-interaction=nonstopmode','c.tex'],cwd=tmp,stdout=subprocess.DEVNULL)
    log=open(tmp+'/c.log').read()
    bad=[l for l in log.split('\n') if l.startswith('!') or 'Missing character' in l]
    if bad: print('\n'.join(bad[:10]))
    dest=R+'/%s/certificate_theorem%d.pdf'%(D,k)
    shutil.copy(tmp+'/c.pdf',dest); print('wrote',dest)

for k in ([int(a) for a in sys.argv[1:]] or [1,2]): build(k)
