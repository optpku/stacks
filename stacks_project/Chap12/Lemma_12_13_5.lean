module

public import Mathlib.Algebra.Homology.QuasiIso
import StacksCheckRecall

@[expose] public section

open CategoryTheory HomologicalComplex ComplexShape

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K L : ChainComplex A ℤ} {f g : K ⟶ L}
variable (h : Homotopy f g) (i : ℤ)

/- Lemma 12.13.5 (1) [0110]: homotopic chain maps induce the same map on homology. -/
@[stacks 0110]
#check (Homotopy.homologyMap_eq h i :
  HomologicalComplex.homologyMap f i = HomologicalComplex.homologyMap g i)

variable (k : K ⟶ L) (hk : HomologicalComplex.homotopyEquivalences A (down ℤ) k)

/- Lemma 12.13.5 (2) [0110]: a homotopy equivalence is a quasi-isomorphism. -/
@[stacks 0110]
#check ((HomologicalComplex.mem_quasiIso_iff k).1
  ((homotopyEquivalences_le_quasiIso A (down ℤ)) k hk) : QuasiIso k)
