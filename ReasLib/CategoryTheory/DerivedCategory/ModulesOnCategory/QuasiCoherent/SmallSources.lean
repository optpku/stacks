/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Complex.Cardinal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.ChaoticClosure
public import ReasLib.CategoryTheory.Pretriangulated.BrownRepresentability.Bounded
public import ReasLib.CategoryTheory.Pretriangulated.BrownRepresentability.SmallSet
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cardinal-bounded sources for quasi-coherent derived modules

This file specializes the cardinal-bounded Brown criterion to the canonical quasi-coherent
subcategory of derived modules on a category with the chaotic topology.
-/

@[expose] public section

noncomputable section

-- Local instance justification (defeq pin): the cardinal function uses the actual
-- ring-sheaf presentation of the existing standard derived localization.
attribute [local instance] RingedSite.Hom.RingPresentation.moduleHasDerivedCategory

open CategoryTheory Limits Opposite
open SheafOfModules.RingedSite

universe u v w

namespace CategoryTheory.ModulesOnCategory.Chaotic

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{max (max u v) w})
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose
  (forget₂ CommRingCat.{max (max u v) w} RingCat.{max (max u v) w})]

/-- The least section-cardinality of a complex representing a canonically quasi-coherent
derived module. -/
@[stacks 0GYZ "size of a quasi-coherent derived module"]
def objectCardinal (K : QC 𝒪) : Cardinal.{max (max u v) w} :=
  SheafOfModules.CochainComplex.derivedObjectCardinal
    (ringSheaf (⊥ : GrothendieckTopology C) 𝒪) K.obj

/-- Canonically quasi-coherent derived modules of section-cardinality at most `kappa`. -/
@[stacks 0GYZ "cardinal-bounded quasi-coherent objects"]
def boundedObjects (kappa : Cardinal.{max (max u v) w}) : Set (QC 𝒪) :=
  BrownRepresentability.Bounded.objects (objectCardinal 𝒪) kappa

/-- Every nonzero canonically quasi-coherent derived module receives a nonzero morphism from a
bounded one. -/
def BoundedObjectsDetectNonzero (kappa : Cardinal.{max (max u v) w}) : Prop :=
  BrownRepresentability.Bounded.DetectsNonzeroObjects (objectCardinal 𝒪) kappa

/-- Maps from bounded quasi-coherent objects into countable coproducts factor through
countable coproducts of bounded quasi-coherent objects. -/
def BoundedObjectsFactorCountableCoproducts
    (kappa : Cardinal.{max (max u v) w}) : Prop :=
  BrownRepresentability.Bounded.FactorsThroughCountableCoproducts
    (objectCardinal 𝒪) kappa

/-- The explicit cardinal of Lemma 21.43.8 (0GYZ): `ℵ₀ + |Arrows(C)| + |∐_U 𝒪(U)|`.

It dominates the three cardinals listed in the source proof: the sizes
`|∐_V j_{U!}𝒪_U(V)|`, the cardinals `max(|𝒪(V)|, |𝒪(U)|, ℵ₀)` of More on Algebra,
`lemma-enlarge`, for all `U ⟶ V`, and the cardinal
`max(ℵ₀, |𝒪(U)|, |Arrows(C)|)` of the subcomplex-generation lemma used by
`lemma-qis-small`. -/
@[stacks 0GYZ "explicit cardinal"]
def sizeBound : Cardinal.{max (max u v) w} :=
  Cardinal.aleph0 + Cardinal.lift.{max (max u v) w} (Cardinal.mk (Σ U V : C, U ⟶ V)) +
    Cardinal.lift.{max (max u v) w} (Cardinal.mk (Σ U : C, 𝒪.val.obj (op U)))

/-- Lemma 21.43.8 (0GYZ) (1) at the explicit cardinal: every nonzero object of `QC 𝒪`
receives a nonzero morphism from an object of size at most `sizeBound 𝒪`. -/
@[stacks 0GYZ "(1)"]
theorem sizeBound_detectNonzero : BoundedObjectsDetectNonzero 𝒪 (sizeBound 𝒪) := sorry

/-- Lemma 21.43.8 (0GYZ) (2) at the explicit cardinal: maps from objects of size at most
`sizeBound 𝒪` into countable coproducts factor through countable coproducts of such
objects. -/
@[stacks 0GYZ "(2)"]
theorem sizeBound_factorCountableCoproducts :
    BoundedObjectsFactorCountableCoproducts 𝒪 (sizeBound 𝒪) := sorry

/-- Lemma 21.43.8 (0GYZ): one cardinal simultaneously supplies nonzero bounded sources for
all nonzero objects of `QC 𝒪` and bounded componentwise factorizations of maps into countable
coproducts.  The witness is the explicit cardinal `sizeBound 𝒪`. -/
@[stacks 0GYZ]
theorem exists_cardinal_for_small_sources :
    ∃ kappa : Cardinal.{max (max u v) w},
      BoundedObjectsDetectNonzero 𝒪 kappa ∧
        BoundedObjectsFactorCountableCoproducts 𝒪 kappa :=
  ⟨sizeBound 𝒪, sizeBound_detectNonzero 𝒪, sizeBound_factorCountableCoproducts 𝒪⟩

/-- The two boundedness clauses identify `boundedObjects 𝒪 kappa` as a
Brown-representability set. -/
theorem boundedObjects_isSet
    {kappa : Cardinal.{max (max u v) w}}
    (hdetect : BoundedObjectsDetectNonzero 𝒪 kappa)
    (hfactor : BoundedObjectsFactorCountableCoproducts 𝒪 kappa) :
    BrownRepresentability.IsSet (boundedObjects 𝒪 kappa) :=
  BrownRepresentability.Bounded.isSet (objectCardinal 𝒪) kappa hdetect hfactor

/-- Raw data of a cochain complex of `𝒪`-modules on the chaotic site whose sections in degree
`i` over `U` form a subset `carrier i U` of a fixed type `X`.  Every field is either data of
the complex (sections, module structures, restrictions, differentials) or one of its laws.
Since `X` and `C` are small, so is the type of all such data; this is how the representatives
of cardinal-bounded objects form a set. -/
structure SectionComplexData (X : Type (max (max u v) w)) where
  /-- The sections in degree `i` over `U`, as a subset of `X`. -/
  carrier : ℤ → C → Set X
  /-- The additive group structure on the sections. -/
  addCommGroup (i : ℤ) (U : C) : AddCommGroup (carrier i U)
  /-- The `𝒪(U)`-module structure on the sections over `U`. -/
  module (i : ℤ) (U : C) :
    letI := addCommGroup i U
    Module ((ringSheaf (⊥ : GrothendieckTopology C) 𝒪).val.obj (op U)) (carrier i U)
  /-- Restriction of sections along `f : U ⟶ V`. -/
  restrict (i : ℤ) {U V : C} (f : U ⟶ V) :
    letI := addCommGroup i V
    letI := addCommGroup i U
    carrier i V →+ carrier i U
  restrict_id (i : ℤ) (U : C) (x : carrier i U) : restrict i (𝟙 U) x = x
  restrict_comp (i : ℤ) {U V W : C} (f : U ⟶ V) (g : V ⟶ W) (x : carrier i W) :
    restrict i (f ≫ g) x = restrict i f (restrict i g x)
  restrict_smul (i : ℤ) {U V : C} (f : U ⟶ V)
      (r : (ringSheaf (⊥ : GrothendieckTopology C) 𝒪).val.obj (op V)) (x : carrier i V) :
    letI := addCommGroup i V
    letI := addCommGroup i U
    letI := module i V
    letI := module i U
    restrict i f (r • x) = (ringSheaf (⊥ : GrothendieckTopology C) 𝒪).val.map f.op r •
      restrict i f x
  /-- The differential in degree `i` over `U`. -/
  diff (i : ℤ) (U : C) :
    letI := addCommGroup i U
    letI := addCommGroup (i + 1) U
    carrier i U →+ carrier (i + 1) U
  diff_smul (i : ℤ) (U : C)
      (r : (ringSheaf (⊥ : GrothendieckTopology C) 𝒪).val.obj (op U)) (x : carrier i U) :
    letI := addCommGroup i U
    letI := addCommGroup (i + 1) U
    letI := module i U
    letI := module (i + 1) U
    diff i U (r • x) = r • diff i U x
  diff_restrict (i : ℤ) {U V : C} (f : U ⟶ V) (x : carrier i V) :
    diff i U (restrict i f x) = restrict (i + 1) f (diff i V x)
  diff_diff (i : ℤ) (U : C) (x : carrier i U) :
    letI := addCommGroup (i + 1 + 1) U
    diff (i + 1) U (diff i U x) = 0

namespace SectionComplexData

variable {𝒪} {X : Type (max (max u v) w)} (d : SectionComplexData 𝒪 X)

/-- The abelian presheaf of degree-`i` sections. -/
def presheaf (i : ℤ) : Cᵒᵖ ⥤ AddCommGrpCat.{max (max u v) w} where
  obj U := @AddCommGrpCat.of (d.carrier i U.unop) (d.addCommGroup i U.unop)
  map {U V} f := by
    letI := d.addCommGroup i U.unop
    letI := d.addCommGroup i V.unop
    exact AddCommGrpCat.ofHom (d.restrict i f.unop)
  map_id U := AddCommGrpCat.ext (fun x ↦ d.restrict_id i U.unop x)
  map_comp f g := AddCommGrpCat.ext (fun x ↦ d.restrict_comp i g.unop f.unop x)

instance (i : ℤ) (U : Cᵒᵖ) :
    Module ((ringSheaf (⊥ : GrothendieckTopology C) 𝒪).val.obj U) ((d.presheaf i).obj U) :=
  d.module i U.unop

/-- The degree-`i` term, a sheaf of `𝒪`-modules (every presheaf is a sheaf for the chaotic
topology). -/
def term (i : ℤ) : SheafOfModules.{max (max u v) w} (ringSheaf (⊥ : GrothendieckTopology C) 𝒪) where
  val := PresheafOfModules.ofPresheaf (d.presheaf i)
    (fun _ _ f r x ↦ d.restrict_smul i f.unop r x)
  isSheaf := Presheaf.isSheaf_bot _

/-- The degree-`i` differential of the complex. -/
def termDiff (i : ℤ) : d.term i ⟶ d.term (i + 1) where
  val := PresheafOfModules.homMk
    { app U := by
        letI := d.addCommGroup i U.unop
        letI := d.addCommGroup (i + 1) U.unop
        exact AddCommGrpCat.ofHom (d.diff i U.unop)
      naturality U V f :=
        AddCommGrpCat.ext (fun x ↦ d.diff_restrict i f.unop x) }
    (fun U r x ↦ d.diff_smul i U.unop r x)

/-- The cochain complex of `𝒪`-modules described by the data. -/
def complex :
    _root_.CochainComplex
      (SheafOfModules.{max (max u v) w} (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)) ℤ :=
  CochainComplex.of d.term d.termDiff (fun i ↦ by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    exact d.diff_diff i U.unop x)

end SectionComplexData

/-- Lemma 21.43.8 (0GYZ): an explicit set of representatives of the canonically
quasi-coherent derived modules of size at most `sizeBound 𝒪`.  Its members are the
quasi-coherent derived objects of complexes whose sections are subsets of
`(sizeBound 𝒪).out`. -/
@[stacks 0GYZ "small Brown-representability set"]
def smallBrownSet : Set (QC 𝒪) :=
  Set.range fun d : {d : SectionComplexData 𝒪 (sizeBound 𝒪).out //
      isQuasiCoherent 𝒪 (DerivedCategory.Q.obj d.complex)} ↦
    (⟨DerivedCategory.Q.obj d.1.complex, d.2⟩ : QC 𝒪)

/-- The explicit representative set is indexed by a type in the coefficient universe. -/
instance smallBrownSet_small : Small.{max (max u v) w} (smallBrownSet 𝒪) := by
  unfold smallBrownSet
  infer_instance

/-- Every explicit representative has size at most `sizeBound 𝒪`. -/
theorem smallBrownSet_subset_boundedObjects :
    smallBrownSet 𝒪 ⊆ boundedObjects 𝒪 (sizeBound 𝒪) := sorry

/-- Every quasi-coherent derived module of size at most `sizeBound 𝒪` is isomorphic to an
explicit representative. -/
theorem exists_mem_smallBrownSet_iso {K : QC 𝒪}
    (hK : K ∈ boundedObjects 𝒪 (sizeBound 𝒪)) :
    ∃ E ∈ smallBrownSet 𝒪, Nonempty (E ≅ K) := sorry

/-- The explicit representatives form a Brown-representability set. -/
@[stacks 0GYZ "Brown-representability set"]
theorem smallBrownSet_isSet : BrownRepresentability.IsSet (smallBrownSet 𝒪) := sorry

/-- The canonical quasi-coherent derived category admits a Brown-representability set. -/
theorem exists_brownSet :
    ∃ S : Set (QC 𝒪), BrownRepresentability.IsSet S :=
  ⟨smallBrownSet 𝒪, smallBrownSet_isSet 𝒪⟩

/-- The cardinal construction supplies representatives forming a Brown set small in the
coefficient universe.  This is the universe-sensitive input used by Brown representability for
the large category `QC 𝒪`. -/
theorem exists_smallBrownSet :
    ∃ S : Set (QC 𝒪), Small.{max (max u v) w} S ∧
      BrownRepresentability.IsSet S :=
  ⟨smallBrownSet 𝒪, smallBrownSet_small 𝒪, smallBrownSet_isSet 𝒪⟩

end CategoryTheory.ModulesOnCategory.Chaotic
