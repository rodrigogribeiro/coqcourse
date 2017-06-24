% O isomorfismo de Curry-Howard
% Ou sobre a similaridade entre provas e programas.
% Rodrigo Ribeiro
---
header-includes:
    - \usepackage{proof}
---

# Slides e materiais para o curso

Todo o material deste curso está disponível no site

http://rodrigogribeiro.github.io/coqcourse


# Logic side: Dedução natural

$$
\Large{
\begin{array}{ccc}
    \dfrac{A \in \Gamma}{\Gamma \vdash A}
	& \hspace{1cm} &
	\dfrac{\Gamma \vdash A \to B\,\,\,\,\,\,\,\Gamma\vdash A}
             {\Gamma \vdash B} \\ \\
    \dfrac{\Gamma \cup \{A\}\vdash B}
              {\Gamma \vdash A \to B} & &
    \dfrac{\Gamma\vdash A\,\,\,\,\,\,\,\Gamma\vdash B}
              {\Gamma \vdash A \land B} \\ \\
    \dfrac{\Gamma \vdash A \land B}
          	{\Gamma \vdash A} & &
    \dfrac{\Gamma \vdash A \land B}
		     {\Gamma \vdash B} 	
\end{array}}
$$

# Type theory side : $\lambda$-cálculo tipado simples

$$
\Large{
\begin{array}{ccc}
    \dfrac{\textcolor[rgb]{1,0,0}{x :}\:A \in \Gamma}{\Gamma \vdash \textcolor[rgb]{1,0,0}{x :}\:A}
	& \hspace{0.1cm} &
	\dfrac{\Gamma \vdash \textcolor[rgb]{1,0,0}{\lambda x. e :}\: A \to
	B\,\,\,\,\,\,\,\Gamma\vdash \textcolor[rgb]{1,0,0}{e' :}\: A}
             {\Gamma \vdash \textcolor[rgb]{1,0,0}{(e\:\:e') :}\: B} \\ \\
    \dfrac{\Gamma \cup \{\textcolor[rgb]{1,0,0}{x :}\: A\}\vdash \textcolor[rgb]{1,0,0}{e :}\: B}
              {\Gamma \vdash \textcolor[rgb]{1,0,0}{\lambda x . e :}\: A \to B} & &
    \dfrac{\Gamma\vdash \textcolor[rgb]{1,0,0}{e :}\: A\,\,\,\,\,\,\,\Gamma\vdash \textcolor[rgb]{1,0,0}{e' :}\: B}
              {\Gamma \vdash \textcolor[rgb]{1,0,0}{(e ,e') :}\: A \times B} \\ \\
    \dfrac{\Gamma \vdash \textcolor[rgb]{1,0,0}{e :}\: A \times B}
          	{\Gamma \vdash \textcolor[rgb]{1,0,0}{fst\:\:e :}\: A} & &
    \dfrac{\Gamma \vdash \textcolor[rgb]{1,0,0}{e :}\: A \times B}
		     {\Gamma \vdash \textcolor[rgb]{1,0,0}{snd\:\:e :}\: B} 	
\end{array}}
$$

# Type theory side : $\lambda$-cálculo tipado simples

$$
\Large{
\begin{array}{ccc}
    \dfrac{\textcolor[rgb]{1,1,1}{x :}\:A \in \Gamma}{\Gamma \vdash \textcolor[rgb]{1,1,1}{x :}\:A}
	& \hspace{0.1cm} &
	\dfrac{\Gamma \vdash \textcolor[rgb]{1,1,1}{\lambda x. e :}\: A \to
	B\,\,\,\,\,\,\,\Gamma\vdash \textcolor[rgb]{1,1,1}{e' :}\: A}
             {\Gamma \vdash \textcolor[rgb]{1,1,1}{(e\:\:e') :}\: B} \\ \\
    \dfrac{\Gamma \cup \{\textcolor[rgb]{1,1,1}{x :}\: A\}\vdash \textcolor[rgb]{1,1,1}{e :}\: B}
              {\Gamma \vdash \textcolor[rgb]{1,1,1}{\lambda x . e :}\: A \to B} & &
    \dfrac{\Gamma\vdash \textcolor[rgb]{1,1,1}{e :}\: A\,\,\,\,\,\,\,\Gamma\vdash \textcolor[rgb]{1,1,1}{e' :}\: B}
              {\Gamma \vdash \textcolor[rgb]{1,1,1}{(e ,e') :}\: A \times B} \\ \\
    \dfrac{\Gamma \vdash \textcolor[rgb]{1,1,1}{e :}\: A \times B}
          	{\Gamma \vdash \textcolor[rgb]{1,1,1}{fst\:\:e :}\: A} & &
    \dfrac{\Gamma \vdash \textcolor[rgb]{1,1,1}{e :}\: A \times B}
		     {\Gamma \vdash \textcolor[rgb]{1,1,1}{snd\:\:e :}\: B} 	
\end{array}}
$$


# Então você percebe...

![The truth](meme.jpg)

# Uma outra visão da lógica.

- Lógica clássica: toda proposição é verdadeira ou falsa.
- Lógica intuicionista: Uma proposição é verdadeira somente se esta
pode ser provada.
    * Mudança de paradigma: verdade sujeita a existência de evidência.
    * Lógica intuicionista é exatamente a lógica clássica sem o axioma
    do terceiro excluído e propriedades derivadas deste.
	* Ao contrário da lógica clássica, a semântica da lógica
      intuicionista é baseada na construção de provas, isto é, na
      dedução natural.

# O isomorfismo de Curry-Howard

- Provas em um dado subconjunto da matemática **correspondem** a programas em uma dada linguagem de programação
     * Descoberto por Curry em '58 e por Howard em '69.
     * Esse "isomorfismo" é também conhecido como "proof-as-programs" correspondence.
- Teoremas nada mais são que tipos e o programa correspondente a
    prova.
      * Para isso, sua linguagem de programação deve ser expressiva.
      * Não tente provar teoremas usando Java, C/C++, Python... :)

# The truth is out there...

\begin{table}
   \begin{tabular}{cc}
        Lógica                & Computação \\
        Provas                & Programas     \\
		Fórmulas            & Tipos  \\ \hline
		Axiomas             & Primitivas de uma linguagem\\
		$A$ implica $B$ & função de $A$ em $B$ \\
		$A$ e $B$           & par formado por $A$ e $B$ \\
		$A$ ou $B$         & tagged union de $A$ e $B$ \\
		falso                   & tipo vazio \\
		verdadeiro          & tipo unit \\
		$\exists x. P(x)$ & um par formado por $x$ e um valor de tipo
		$P(x)$\\
		$\forall x \in A. P(x)$ & uma função de $x : A$ em $P(x)$.
   \end{tabular}
\end{table}

# The truth is out there...

- Composição de funções

```haskell
comp :: (B -> C) -> (A -> B) -> A -> C
comp = \ f -> \ g -> \ x -> f (g x)
```

# The truth is out there...

$$\Gamma = \{f : B \to C, g : A \to B, x : A\}$$


\small{
\infer{\emptyset \vdash \lambda f : B \to C. \lambda g : A \to B. \lambda x : A. f\:(g\:\:x) : (B\to C)\to (A \to B) \to A \to C }
         {\infer{\{f : B \to C\}\vdash \lambda g : A \to B. \lambda x : A. f\:(g\:\:x) : (A \to B) \to A \to C}
		           {\infer{\{f : B \to C, g : A \to B\}\vdash \lambda x : A. f\:(g\:\:x) : A \to C}
				             {\infer{\{f : B \to C, g : A \to B, x : A\}\vdash f\:(g\:\:x) : C}
							 {\infer {\Gamma \vdash f : B \to C}
						          	    {f : B \to C \in \Gamma}
							            &
	                         \infer{\Gamma \vdash (g\:\:x) : B}
								      {\infer{\Gamma \vdash g : A \to B}
									            {g : A \to B \in \Gamma}
												&
                                       \infer{\Gamma\vdash x : A}
												{x : A \in \Gamma} } }  }  }  }

}

# The truth is out there...

\large{
\infer{\emptyset \vdash (B\to C)\to (A \to B) \to A \to C }
         {\infer{\{B \to C\}\vdash (A \to B) \to A \to C}
		           {\infer{\{B \to C, A \to B\}\vdash A \to C}
				             {\infer{\{B \to C, A \to B, A\}\vdash C}
							 {\infer {\Gamma \vdash B \to C}
						          	    {B \to C \in \Gamma}
							            &
	                         \infer{\Gamma \vdash B}
								      {\infer{\Gamma \vdash A \to B}
									            {A \to B \in \Gamma}
												&
                                       \infer{\Gamma\vdash A}
												{A \in \Gamma} } }  }  }  }

}

# The truth is out there...

O termo $$\lambda f. \lambda g. \lambda x . f\:(g\:\: x)$$ pode ser
considerado uma representação da derivação, em dedução natural, da
fórmula $$(B \to C)\to (A \to B)\to A \to C$$, que é o tipo da função
anterior.

# The truth is out there...

- Não é só isso: provas por indução são funções recursivas!

- Teorema: Para todo $n \in \mathbb{N}$, existe $p\in\mathbb{N}$
tal que $n = 2p$ ou $n = 2p + 1$.

    * Caso $n = 0$. Imediato.
	* Caso $n = m + 1$. Pela I.H. temos que existe $p$ tal que
	  $m = 2p$ ou $m = 2p + 1$.
	     * Caso $m = 2p$: temos que $n = 2p + 1$.
	     * Caso $m = 2p + 1$: temos que $n = 2 (p + 1)$

# The truth is out there...

- Não é só isso: provas por indução são funções recursivas!

```haskell
div2 :: Int -> (Int, Bool)
div2 n
     | n == 0     = (0,True)
     | otherwise = if even then (p ,false)
	                        else (p + 1, true)
      	where
             (p,even) = div2 (n - 1)
````

# A new hope...

$$
\begin{array}{ccc}
  \text{Novos axiomas}          & \sim & \text{Novas primitivas} \\
  \Updownarrow                     &          & \Updownarrow \\
  \text{Representação lógica} & \sim  & \text{Transformação de programas}\\
\end{array}
$$

# A new hope...

- Princípios da lógica clássica, usados cotidianamente por
  programadores JS

$$
\begin{array}{ccc}
  \text{Novos axiomas}          &          & \text{Novas primitivas} \\
         A \lor \neg A                 & \sim  & \texttt{callcc} \\
   \Updownarrow                    &          & \Updownarrow \\
  \text{Representação lógica} &          & \text{Transformação de programas}\\
    \text{double negation}       & \sim  & \text{callback-passing style}\\
\end{array}
$$

# Novas perspectivas de pesquisa

- A relação entre lógica e computação é um campo frutífero de
pesquisa!
- Homotopy type theory
   * Provas como paths, tipos são homotopy spaces
   * Novas perspectivas sobre a definição de igualdade em assistentes
     de provas.

# O assistente de provas Coq

- Ferramenta que explora o isomorfismo de Curry-Howard.
- Desenvolvido pelo Inria, França desde 1984.
- Vencedor do ACM Software System Award, 2013

# Afinal, onde isso é utilizado?

- Matemática
    * Teorema das 4 cores.
    * Teorema de Feit-Thomson.
	* Formalizações da homotopy type theory.
- Computação
    * Compilador de C/C++ (Compcert)
    * Ferramenta para criação de blogs
	* Bibliotecas para verificação de programas C usando separation
    logic.
	
# Moral da história

- Tipos são fórmulas da lógica, programas são provas!
- Verificar uma prova nada mais é que o processo de verificação de
tipos realizado por um compilador.
- Em essência, lógica e computação são visões diferentes de um mesmo fenômeno.

# Slides e materiais para o curso

Todo o material deste curso está disponível no site

http://rodrigogribeiro.github.io/coqcourse
