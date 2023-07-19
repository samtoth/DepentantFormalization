One of the motivating ideas of this project is that there a lot of new ideas in type theories being tested out, but in each new iteration poeple are having to rebuild alot of the same tools and functionality again and again. I think this goes against common software engineering good practices. It seems that what makes a good proof assistant is largely invariant under what the actual core theory is that you are working in. At the same time, it isn’t possible or realistic to hope to cover all different type theories that have or will be constructed so when designing the core language layer of the proof assistant the goal is to cover a wide enough range of possible theories whilst still actually reducing the amount of work in developing a new theory. For example, it probably is not all that useful to state that a Type Theory is any well founded tree of expressions. Acknowledging my own bias, and what seems to be most actively researched at the moment, the core language will have a certain _Martin-Löf_-ian twinge to it.

### What is in common.
- In almost all cases there are a handful of primitive judgements that are used to define a type theory.
    - There are some type of **Contexts** and these must be well formed.
    - There are some Context indexed family of **Types** and these have judgements regarding their well-foundedness and of type equality.
    - There are Type and Context indexed families of **Terms** which have judgments of their well typedness, equality and reduction rules.
- In all type theories there are bindings are variables - which can often be fiddley but essentially uninteresting to implement.

### Univalence
The principal that equivalent structures should have the same properties seems quite important for building up libraries that can work together nicely. To borrow more ideas from computer science - it is better practices to have lots of libraries that cover one specific functionality or topic than huge monolithic libraries as in MathLib for Lean. It seems that the one way this can be possible is with Univalent foundations. Again, as a computer scientist it would be nice to work with constructive foundations and therefor cubical type methods seem to be our best current technique for working with HoTT constructively; the core type theory should be general enough to support various cubical methods (CCHM or ABCHHL).

### Having it all!
Inspired by [ANDERS](https://www.notion.so/MODAL-HOMOTOPY-TYPE-SYSTEM-d7b7fd12a3d84d52aae04f71c5665c77?pvs=21), we can use a technique whereby there are multiple [[universe hierarchies ]] that coexist which represent different type schemes. For example you might want a universe of types with strict equality (i.e. uniqueness of identity proofs - henceforth UIP);  as well as a univalent universe of fibrant types as well as Pretypes for cubical Intervals. Other examples could be a predicative universe of Propositions - $Prop$, or a universe of opetopic types $\mathcal{O}$. In general this can be called a multi-level type system. (see [ncatlab](https://ncatlab.org/nlab/show/two-level+type+theory) for details on two-level type systems).

### Computational HoTT
In Andromeda, despite being capable of having user defined core theories, they explicitly don't  support cubical type systems, due to them having a special kind of type called a pretype - which the interval falls in to. They also have special additional requirements on the context - called fibrations ($\mathcal{F}$), also known as face maps which allow you to define so called partial types. 

### Inspiration
[Andromeda](https://math.andrej.com/wp-content/uploads/2019/08/derivations-as-computations-icfp-2019.pdf)