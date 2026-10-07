module

public import ReasLib.Algebra.Homology.HomologicalComplex.KernelAcyclic
public import ReasLib.AlgebraicTopology.DoldKan.Equivalence
public import ReasLib.AlgebraicTopology.SimplicialObject.Grp.KanFibration
public import ReasLib.AlgebraicTopology.SimplicialObject.Underlying.TrivialKanFibration
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 08P1

# Dold--Kan criteria for trivial Kan fibrations

The normalized Moore and alternating-face complexes detect the same quasi-isomorphisms. For
simplicial abelian groups, a degreewise-surjective such map is a trivial Kan fibration after
forgetting to simplicial sets.
-/

@[expose] public section

open CategoryTheory.Limits Opposite
open AlgebraicTopology AlgebraicTopology.DoldKan
open SSet.modelCategoryQuillen

universe v u

namespace CategoryTheory.SimplicialObject

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace AddCommGrp

variable {X Y : SimplicialObject AddCommGrpCat.{u}}

namespace underlying

namespace trivialKanFibrations

/-- Epimorphic normalized-Moore quasi-isomorphisms of simplicial abelian groups form a
subproperty of the underlying trivial Kan fibrations. -/
@[stacks 08P1 "normalized-Moore criterion for underlying trivial Kan fibrations"]
theorem normalizedMoore :
    (MorphismProperty.epimorphisms (SimplicialObject AddCommGrpCat.{u}) ⊓
      (HomologicalComplex.quasiIso AddCommGrpCat.{u} (ComplexShape.down ℕ)).inverseImage
        (normalizedMooreComplex AddCommGrpCat.{u})) ≤
      Underlying.trivialKanFibrations (forget AddCommGrpCat) := sorry

/-- Epimorphic alternating-face quasi-isomorphisms of simplicial abelian groups form a
subproperty of the underlying trivial Kan fibrations. -/
@[stacks 08P1 "alternating-face criterion for underlying trivial Kan fibrations"]
theorem alternatingFace :
    (MorphismProperty.epimorphisms (SimplicialObject AddCommGrpCat.{u}) ⊓
      (HomologicalComplex.quasiIso AddCommGrpCat.{u} (ComplexShape.down ℕ)).inverseImage
        (alternatingFaceMapComplex AddCommGrpCat.{u})) ≤
      Underlying.trivialKanFibrations (forget AddCommGrpCat) := sorry

namespace normalizedMoore

/-- An epimorphic normalized-Moore quasi-isomorphism of simplicial abelian groups is a trivial Kan
fibration on underlying simplicial sets. -/
@[stacks 08P1 "trivial Kan fibration criterion for simplicial abelian groups"]
theorem of_epi {f : X ⟶ Y} [Epi f]
    [QuasiIso ((normalizedMooreComplex AddCommGrpCat.{u}).map f)] :
    I.rlp (Functor.whiskerRight f (forget AddCommGrpCat)) := sorry

/-- The degreewise-surjective normalized-Moore criterion with explicit assumptions. -/
@[stacks 08P1 "surjective normalized-Moore criterion with explicit assumptions"]
theorem of_surjective {f : X ⟶ Y}
    (hsurjective : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n))
    (hquasi : QuasiIso ((normalizedMooreComplex AddCommGrpCat.{u}).map f)) :
    I.rlp (Functor.whiskerRight f (forget AddCommGrpCat)) := sorry

end normalizedMoore

namespace alternatingFace

/-- An epimorphic alternating-face quasi-isomorphism of simplicial abelian groups is a trivial
Kan fibration on underlying simplicial sets. -/
@[stacks 08P1 "categorical alternating-face trivial Kan fibration criterion"]
theorem of_epi {f : X ⟶ Y} [Epi f]
    [QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map f)] :
    I.rlp (Functor.whiskerRight f (forget AddCommGrpCat)) := sorry

/-- The degreewise-surjective alternating-face criterion with explicit assumptions. -/
@[stacks 08P1 "surjective alternating-face criterion with explicit assumptions"]
theorem of_surjective {f : X ⟶ Y}
    (hsurjective : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n))
    (hquasi : QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map f)) :
    I.rlp (Functor.whiskerRight f (forget AddCommGrpCat)) := sorry

end alternatingFace

end trivialKanFibrations

end underlying

end AddCommGrp

end CategoryTheory.SimplicialObject

open CategoryTheory

namespace AlgebraicTopology.normalizedMooreComplex

/-- The normalized-Moore and alternating-face functors pull back the chain-complex
quasi-isomorphism property to the same morphism property of simplicial objects. -/
@[stacks 08P1 "normalized and alternating quasi-isomorphism properties"]
theorem quasiIso_eq_alternatingFace {A : Type u} [Category.{v} A] [Abelian A] :
    (HomologicalComplex.quasiIso A (ComplexShape.down ℕ)).inverseImage
        (normalizedMooreComplex A) =
      (HomologicalComplex.quasiIso A (ComplexShape.down ℕ)).inverseImage
        (alternatingFaceMapComplex A) := sorry

/-- A simplicial morphism induces a quasi-isomorphism on its normalized Moore complex exactly when
it does so on its alternating-face complex. -/
@[stacks 08P1 "normalized and alternating Dold-Kan quasi-isomorphisms"]
theorem map.quasiIso_iff_alternatingFace {A : Type u} [Category.{v} A] [Abelian A]
    {X Y : SimplicialObject A} (f : X ⟶ Y) :
    QuasiIso ((normalizedMooreComplex A).map f) ↔
      QuasiIso ((alternatingFaceMapComplex A).map f) := sorry

/-- The normalized Moore complex of the kernel of an epimorphic quasi-isomorphism is acyclic. -/
@[stacks 08P1 "acyclic normalized Moore complex of a simplicial kernel"]
theorem kernel.acyclic_of_epi {A : Type u} [Category.{v} A] [Abelian A]
    {X Y : SimplicialObject A} {f : X ⟶ Y} [Epi f]
    [QuasiIso ((normalizedMooreComplex A).map f)] :
    ((normalizedMooreComplex A).obj (kernel f)).Acyclic := sorry

/-- Explicit-proof bridge for acyclicity of the normalized Moore kernel of an epimorphism. -/
@[stacks 08P1 "acyclic normalized Moore kernel with explicit assumptions"]
theorem kernel.acyclic_of_epi.explicit {A : Type u} [Category.{v} A] [Abelian A]
    {X Y : SimplicialObject A} {f : X ⟶ Y}
    (hepi : Epi f) (hquasi : QuasiIso ((normalizedMooreComplex A).map f)) :
    ((normalizedMooreComplex A).obj (kernel f)).Acyclic := sorry

end AlgebraicTopology.normalizedMooreComplex
