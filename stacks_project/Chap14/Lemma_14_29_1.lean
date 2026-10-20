module

public import ReasLib.Algebra.Homology.Homotopy.Cylinder
import StacksCheckRecall

/-!
@stack 01A2
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

noncomputable section

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (A : ChainComplex C ℤ)

/- Lemma 14.29.1 (1): the canonical cylinder of `A` corepresents the functor sending a chain
complex `B` to two maps `A ⟶ B` equipped with a homotopy between them. -/
@[stacks 01A2 "Lemma 14.29.1 (1)"]
#check (HomologicalComplex.cylinder.corepresentableBy
  (C := C) (c := ComplexShape.down ℤ) A :
  (HomologicalComplex.HomotopyTriple.functor A).CorepresentableBy A.cylinder)

/- Lemma 14.29.1 (2): the canonical cylinder construction is functorial on `ℤ`-indexed chain
complexes; its action is induced directly by functoriality of homotopy cofibers. -/
@[stacks 01A2 "Lemma 14.29.1 (2)"]
#check (HomologicalComplex.cylinder.functor
  (C := C) (c := ComplexShape.down ℤ) :
  ChainComplex C ℤ ⥤ ChainComplex C ℤ)

/- The two endpoint inclusions and the cylinder projection are reusable natural
transformations. -/
#check HomologicalComplex.cylinder.ι₀.natTrans
#check HomologicalComplex.cylinder.ι₁.natTrans
#check HomologicalComplex.cylinder.π.natTrans
