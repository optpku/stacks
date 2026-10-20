/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Spectrum
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.FieldPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.Action

/-!
# The generic point of the affine-line translation quotient

The fppf quotient sheaf of the integer translation action, its generic-point morphism, and
its self-pullback comparison are recorded here.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PreRelation
open IsLocalRing
open AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient
open AlgebraicGeometry.FieldExtension

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation

/-- The fppf sheaf quotient of the integer translation action. -/
def sheafOfPoints (k : Type u) [Field k] [CharZero k] :
    Sheaf (Scheme.fppfTopology.over (AffineLineQuotient.base k)) (Type (u + 1)) :=
  (ofAut (action k)).quotientSheaf (Scheme.fppfTopology.over (AffineLineQuotient.base k))

/-- The canonical quotient atlas from the affine line. -/
def atlas (k : Type u) [Field k] [CharZero k] :
    (Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.obj
        (AffineLineQuotient.cover k) ⟶ sheafOfPoints k :=
  (ofAut (action k)).quotientMap (Scheme.fppfTopology.over (AffineLineQuotient.base k))

/-- The quotient sheaf has representable diagonal. -/
theorem representableDiagonal_sheafOfPoints (k : Type u) [Field k] [CharZero k] :
    uliftYoneda.{u + 1}.relativelyRepresentable (diag (sheafOfPoints k).obj) := by sorry

/-- The quotient atlas is representable and étale. -/
theorem atlas_etale (k : Type u) [Field k] [CharZero k] :
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} (atlas k).hom := by sorry

/-- The quotient atlas is étale-locally surjective. -/
instance atlas_locallySurjective (k : Type u) [Field k] [CharZero k] :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (AffineLineQuotient.base k))
      (atlas k).hom := by sorry

/-- The residue field at the generic point of the affine line. -/
abbrev genericResidueField (k : Type u) [Field k] [CharZero k] : Type u :=
  ResidueField ((AffineLineQuotient.cover k).left.presheaf.stalk
    (genericPoint (AffineLineQuotient.cover k).left))

/-- The structure morphism of the generic residue-field spectrum to the base. -/
def genericStructure (k : Type u) [Field k] [CharZero k] :
    Spec (CommRingCat.of (genericResidueField k)) ⟶ AffineLineQuotient.base k :=
  (AffineLineQuotient.cover k).left.fromSpecResidueField
      (genericPoint (AffineLineQuotient.cover k).left) ≫ (AffineLineQuotient.cover k).hom

/-- The algebra structure induced on the generic residue field by the structure morphism. -/
instance instAlgebra_genericResidueField (k : Type u) [Field k] [CharZero k] :
    Algebra k (genericResidueField k) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (genericStructure k).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of (genericResidueField k))).hom).hom.toAlgebra

/-- The generic residue-field spectrum as an object over the base. -/
abbrev genericOver (k : Type u) [Field k] [CharZero k] :
    Over (AffineLineQuotient.base k) :=
  specOver (genericStructure k)

/-- The generic point of the affine line as a morphism over the base. -/
def genericToCover (k : Type u) [Field k] [CharZero k] :
    genericOver k ⟶ AffineLineQuotient.cover k :=
  Over.homMk ((AffineLineQuotient.cover k).left.fromSpecResidueField
    (genericPoint (AffineLineQuotient.cover k).left)) rfl

/-- The underlying scheme map of the generic point morphism. -/
theorem genericToCover_left (k : Type u) [Field k] [CharZero k] :
    (genericToCover k).left =
      (AffineLineQuotient.cover k).left.fromSpecResidueField
        (genericPoint (AffineLineQuotient.cover k).left) := by rfl

/-- The canonical generic-point morphism to the quotient sheaf. -/
def genericHom (k : Type u) [Field k] [CharZero k] :
    specToQuotientHom (action k) (genericStructure k) :=
  (Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map
      (genericToCover k) ≫ atlas k

/-- The generic point morphism lifts to the quotient atlas. -/
theorem isQuotientLift_genericToCover (k : Type u) [Field k] [CharZero k] :
    (Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map
        (genericToCover k) ≫ atlas k = genericHom k := by rfl

/-- Any monomorphic field-spectrum factorization of the generic point has an isomorphic
intervening spectrum map. -/
theorem isIso_of_mono_factor (k : Type u) [Field k] [CharZero k]
    {L : Type u} [Field L] [Algebra k L]
    (ι : specToQuotientHom (action k) (FieldExtension.specMap k L))
    (φ : genericOver k ⟶ specOver (FieldExtension.specMap k L))
    (hι : CategoryTheory.Mono ι)
    (hφ :
      (Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map φ ≫ ι =
        genericHom k) :
    IsIso φ.left := by sorry

/-- The coproduct of generic residue-field spectra indexed by the acting group. -/
def genericCoproduct (k : Type u) [Field k] [CharZero k] :
    Over (AffineLineQuotient.base k) :=
  ∐ fun _ : group ↦ genericOver k

/-- The automorphism of the generic residue field fixes the base structure map. -/
theorem genericAut_w (k : Type u) [Field k] [CharZero k] (g : group) :
    Spec.map (genericResidueAut k g) ≫ (genericOver k).hom = (genericOver k).hom := by sorry

/-- The automorphism of the generic spectrum induced by a translation. -/
def genericAut (k : Type u) [Field k] [CharZero k] (g : group) :
    genericOver k ⟶ genericOver k :=
  Over.homMk (Spec.map (genericResidueAut k g)) (genericAut_w k g)

/-- The underlying scheme map of the generic-spectrum automorphism. -/
theorem genericAut_left (k : Type u) [Field k] [CharZero k] (g : group) :
    (genericAut k g).left = Spec.map (genericResidueAut k g) := by rfl

/-- The first projection from the indexed coproduct to the generic spectrum. -/
def genericCoproductFst (k : Type u) [Field k] [CharZero k] :
    genericCoproduct k ⟶ genericOver k :=
  Sigma.desc fun g : group ↦ genericAut k g

/-- The second projection from the indexed coproduct to the generic spectrum. -/
def genericCoproductSnd (k : Type u) [Field k] [CharZero k] :
    genericCoproduct k ⟶ genericOver k :=
  Sigma.desc fun _ : group ↦ 𝟙 (genericOver k)

/-- Translation on the generic spectrum composes trivially with the quotient morphism. -/
theorem genericAut_comp_genericHom (k : Type u) [Field k] [CharZero k] (g : group) :
    (Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map
        (genericAut k g) ≫ genericHom k = genericHom k := by sorry

/-- The two coproduct projections become equal after composition with the generic quotient map. -/
theorem genericCoproduct_equalizes (k : Type u) [Field k] [CharZero k] :
    (Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map
        (genericCoproductFst k) ≫ genericHom k =
      (Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map
        (genericCoproductSnd k) ≫ genericHom k := by sorry

/-- The comparison map from the indexed coproduct to the generic-point self-pullback. -/
def genericPullbackIso_inv (k : Type u) [Field k] [CharZero k] :
    (Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.obj
        (genericCoproduct k) ⟶ pullback (genericHom k) (genericHom k) :=
  pullback.lift
    ((Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map
      (genericCoproductFst k))
    ((Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map
      (genericCoproductSnd k))
    (genericCoproduct_equalizes k)

/-- The first projection of the comparison map is the first coproduct projection. -/
theorem genericPullbackIso_inv_fst (k : Type u) [Field k] [CharZero k] :
    genericPullbackIso_inv k ≫ pullback.fst (genericHom k) (genericHom k) =
      (Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map
        (genericCoproductFst k) := by
  simpa [genericPullbackIso_inv] using
    (pullback.lift_fst
      ((Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map
        (genericCoproductFst k))
      ((Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map
        (genericCoproductSnd k))
      (genericCoproduct_equalizes k))

/-- The second projection of the comparison map is the second coproduct projection. -/
theorem genericPullbackIso_inv_snd (k : Type u) [Field k] [CharZero k] :
    genericPullbackIso_inv k ≫ pullback.snd (genericHom k) (genericHom k) =
      (Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map
        (genericCoproductSnd k) := by
  simpa [genericPullbackIso_inv] using
    (pullback.lift_snd
      ((Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map
        (genericCoproductFst k))
      ((Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map
        (genericCoproductSnd k))
      (genericCoproduct_equalizes k))

/-- The coproduct comparison map is an isomorphism of fppf sheaves. -/
instance instIsIso_genericPullbackIso_inv (k : Type u) [Field k] [CharZero k] :
    IsIso (genericPullbackIso_inv k) := by sorry

/-- The generic-point morphism is not monic. -/
theorem not_mono_genericHom (k : Type u) [Field k] [CharZero k] :
    ¬ CategoryTheory.Mono (genericHom k) := by sorry

/-- The generic-point morphism does not factor through a monomorphism from a field spectrum. -/
theorem not_exists_mono_factor (k : Type u) [Field k] [CharZero k] :
    ¬ ∃ (L : Type u) (_ : Field L) (_ : Algebra k L)
        (ι : specToQuotientHom (action k) (FieldExtension.specMap k L))
        (hι : CategoryTheory.Mono ι)
        (φ : genericOver k ⟶ specOver (FieldExtension.specMap k L)),
        (Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map φ ≫ ι =
          genericHom k := by sorry

end AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation
