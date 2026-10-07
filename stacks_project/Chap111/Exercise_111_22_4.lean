module

public import ReasLib.RingTheory.PicardGroup.Node
import StacksCheckRecall

@[expose] public section

universe u

open CommRing MvPolynomial

section

variable {k : Type u} [Field k]

/- Exercise 111.22.4 (1): the class group of the polynomial ring `Polynomial k` over a field
`k` is trivial. -/
@[stacks 078R]
#check (CommRing.Pic.subsingletonPolynomial : Subsingleton (Pic (Polynomial k)))

end

/- Exercise 111.22.4 (2): the class group of `ℤ` is trivial. -/
@[stacks 078R]
#check (CommRing.Pic.subsingletonInt : Subsingleton (Pic ℤ))

section

variable {k : Type u} [Field k]

/- Exercise 111.22.4 (3): the class group of `MvPolynomial (Fin 2) k` over a field `k` is
trivial. -/
@[stacks 078R]
#check (CommRing.Pic.subsingletonMvPolynomial : Subsingleton (Pic (MvPolynomial (Fin 2) k)))

end

section

variable {k : Type u} [Field k]

/- Exercise 111.22.4 (4): the class group of
`MvPolynomial (Fin 2) k ⧸ Ideal.span {X 0 * X 1}` over a field `k` is trivial. -/
@[stacks 078R]
#check (CommRing.Pic.instSubsingletonQuotientSpanMul :
  Subsingleton (CommRing.Pic (MvPolynomial (Fin 2) k ⧸
    Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) k)})))

end
