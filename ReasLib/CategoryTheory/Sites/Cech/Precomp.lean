module

public import ReasLib.CategoryTheory.Sites.Cech.Basic
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Map
public import ReasLib.CategoryTheory.Limits.FiniteNonempty.Preserves
public import Mathlib.CategoryTheory.Limits.Preserves.Lattice
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cech complexes and finite-nonempty-limit-preserving precomposition

A functor which preserves finite nonempty limits carries the nonempty finite intersections
occurring in a Cech nerve to the corresponding intersections in the target.  This file records
the resulting canonical comparison before specializing it to inverse images of open subsets.
-/

@[expose] public section

open AlgebraicTopology CategoryTheory.Limits Opposite

noncomputable section

universe w t v v' vA u u' uA

namespace CategoryTheory.Limits.FormalCoproduct

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]

variable [HasFiniteProducts C] [HasFiniteProducts D]

/-- The diagram obtained by mapping a discrete family is canonically isomorphic to the discrete
diagram of its componentwise image. -/
noncomputable def mapPowerDiagramIso (L : C ⥤ D) (U : FormalCoproduct.{w} C)
    {J : Type t} (i : J → U.I) :
    Discrete.functor (U.obj ∘ i) ⋙ L ≅
      Discrete.functor (((map L).obj U).obj ∘ i) :=
  Discrete.natIso fun _ ↦ Iso.refl _

/-- The component comparison between the image of a nonempty finite product and the product of
the componentwise images. -/
noncomputable def mapPowerComponentIso (L : C ⥤ D) [PreservesFiniteNonemptyLimits L]
    (U : FormalCoproduct.{w} C) {J : Type t} [Fintype J] [Nonempty J] (i : J → U.I) :
    L.obj (∏ᶜ (U.obj ∘ i)) ≅ ∏ᶜ (((map L).obj U).obj ∘ i) :=
  preservesLimitIso L (Discrete.functor (U.obj ∘ i)) ≪≫
    Limits.lim.mapIso (mapPowerDiagramIso L U i)

/-- A functor preserving finite nonempty limits identifies the image of a nonempty finite power
of a formal coproduct with the corresponding power of its componentwise image. -/
noncomputable def mapPowerIso (L : C ⥤ D) [PreservesFiniteNonemptyLimits L]
    (U : FormalCoproduct.{w} C) (J : Type t) [Fintype J] [Nonempty J] :
    (map L).obj (U.power J) ≅ ((map L).obj U).power J :=
  FormalCoproduct.isoOfComponents (Equiv.refl _)
    (mapPowerComponentIso L U)

/-- The nonempty finite-power comparison is compatible with maps of the indexing finite sets. -/
theorem mapPowerIso_naturality (L : C ⥤ D) [PreservesFiniteNonemptyLimits L]
    (U : FormalCoproduct.{w} C) {J K : Type t} [Fintype J] [Nonempty J]
    [Fintype K] [Nonempty K]
    (f : J → K) :
    (map L).map (U.mapPower f) ≫ (mapPowerIso L U J).hom =
      (mapPowerIso L U K).hom ≫ ((map L).obj U).mapPower f := sorry

/-- A functor preserving finite nonempty limits commutes canonically with the Cech simplicial
object of a formal coproduct. -/
@[stacks 01FD "finite-nonempty-limit preservation and Cech nerves"]
noncomputable def mapCechIso (L : C ⥤ D) [PreservesFiniteNonemptyLimits L]
    (U : FormalCoproduct.{w} C) :
    U.cech ⋙ map L ≅ ((map L).obj U).cech :=
  NatIso.ofComponents
    (fun n ↦ mapPowerIso L U (ToType n.unop))
    (fun f ↦ mapPowerIso_naturality L U f.unop.toOrderHom.toFun)

variable {A : Type uA} [Category.{vA} A] [HasProducts.{w} A]

/-- Precomposing coefficients by `L.op` and evaluating on a formal coproduct agrees strictly with
evaluating on its componentwise image under `L`. -/
noncomputable def evalOpPrecompIso (L : C ⥤ D) :
    (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj L.op ⋙ evalOp C A ≅
      evalOp D A ⋙
        (Functor.whiskeringLeft (FormalCoproduct.{w} C)ᵒᵖ
          (FormalCoproduct.{w} D)ᵒᵖ A).obj (map L).op :=
  Iso.refl _

end CategoryTheory.Limits.FormalCoproduct

namespace CategoryTheory.Cech.Precomp

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
variable {D : Type u'} [Category.{v'} D] [HasFiniteProducts D]
variable {A : Type uA} [Category.{vA} A] [HasProducts.{w} A] [Preadditive A]

/-- The source cosimplicial-object functor obtained by precomposing coefficients with a functor
preserving finite nonempty limits. -/
abbrev cosimplicialSource (L : C ⥤ D) (U : FormalCoproduct.{w} C) :
    (Dᵒᵖ ⥤ A) ⥤ CosimplicialObject A :=
  (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj L.op ⋙
    FormalCoproduct.cosimplicialObjectFunctor U.cech

/-- The target Cech cosimplicial-object functor for the componentwise image of a formal
coproduct. -/
abbrev cosimplicialTarget (L : C ⥤ D) (U : FormalCoproduct.{w} C) :
    (Dᵒᵖ ⥤ A) ⥤ CosimplicialObject A :=
  FormalCoproduct.cosimplicialObjectFunctor ((FormalCoproduct.map L).obj U).cech

/-- The component at a simplex of the canonical Cech cosimplicial comparison. -/
noncomputable def component
    (L : C ⥤ D) [PreservesFiniteNonemptyLimits L]
    (U : FormalCoproduct.{w} C) (P : Dᵒᵖ ⥤ A) (n : SimplexCategory) :
    ((cosimplicialSource (A := A) L U).obj P).obj n ≅
      ((cosimplicialTarget (A := A) L U).obj P).obj n :=
  ((FormalCoproduct.evalOp D A).obj P).mapIso
    (FormalCoproduct.mapPowerIso L U (ToType n)).symm.op

/-- The simplex components of the Cech precomposition comparison are cosimplicially natural. -/
theorem component_naturality
    (L : C ⥤ D) [PreservesFiniteNonemptyLimits L]
    (U : FormalCoproduct.{w} C) (P : Dᵒᵖ ⥤ A)
    {m n : SimplexCategory} (f : m ⟶ n) :
    ((cosimplicialSource (A := A) L U).obj P).map f ≫
        (component (A := A) L U P n).hom =
      (component (A := A) L U P m).hom ≫
        ((cosimplicialTarget (A := A) L U).obj P).map f := sorry

/-- The canonical comparison of Cech cosimplicial objects at one coefficient presheaf. -/
noncomputable def appIso
    (L : C ⥤ D) [PreservesFiniteNonemptyLimits L]
    (U : FormalCoproduct.{w} C) (P : Dᵒᵖ ⥤ A) :
    (cosimplicialSource (A := A) L U).obj P ≅
      (cosimplicialTarget (A := A) L U).obj P :=
  NatIso.ofComponents
    (component (A := A) L U P)
    (component_naturality (A := A) L U P)

/-- The Cech cosimplicial comparison is natural in the coefficient presheaf. -/
theorem appIso_naturality
    (L : C ⥤ D) [PreservesFiniteNonemptyLimits L]
    (U : FormalCoproduct.{w} C) {P Q : Dᵒᵖ ⥤ A} (f : P ⟶ Q) :
    (cosimplicialSource (A := A) L U).map f ≫
        (appIso (A := A) L U Q).hom =
      (appIso (A := A) L U P).hom ≫
        (cosimplicialTarget (A := A) L U).map f := sorry

/-- Precomposing a presheaf by a functor preserving finite nonempty limits commutes canonically
with the Cech cosimplicial-object construction. -/
noncomputable def iso
    (L : C ⥤ D) [PreservesFiniteNonemptyLimits L]
    (U : FormalCoproduct.{w} C) :
    cosimplicialSource (A := A) L U ≅
      cosimplicialTarget (A := A) L U :=
  NatIso.ofComponents
    (appIso (A := A) L U)
    (appIso_naturality (A := A) L U)

/-- The Cech complex of coefficients precomposed by a functor preserving finite nonempty limits
is canonically isomorphic to the Cech complex on the image family. -/
@[stacks 01FD "Cech complexes and finite-nonempty-limit-preserving precomposition"]
noncomputable def complexIso
    (L : C ⥤ D) [PreservesFiniteNonemptyLimits L] {I : Type w} (U : I → C) :
    (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj L.op ⋙ cechComplexFunctor U ≅
      cechComplexFunctor (fun i ↦ L.obj (U i)) :=
  (Functor.associator
      ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj L.op)
      (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk I U).cech)
      (alternatingCofaceMapComplex A)).symm ≪≫
    Functor.isoWhiskerRight
      (iso (A := A) L (FormalCoproduct.mk I U))
      (alternatingCofaceMapComplex A)

end CategoryTheory.Cech.Precomp
