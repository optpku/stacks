module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Tensor
public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Tensor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change for extended alternating Cech complexes

The principal-localization family, its Cech conerve, and the extended alternating complex all
commute with extension of scalars.  The module-valued result is assembled from the ring-valued
comparison, the tensor description, and the tensor/extension reassociation.

@stack 0G6I
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits ComplexShape ModuleCat MonoidalCategory
open AlgebraicTopology LocalizedModule
open scoped TensorProduct

namespace LocalizedModule.Away.Cech.Alternating.BaseChange

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {r : ℕ}

-- Local instance justification (instance diamond): the target-side tensor action is needed only
-- while normalizing extension of scalars, and exporting it would compete with the left action.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Extension of scalars on modules. -/
@[stacks 0G6I "scalar-extension functor for Cech base change"]
abbrev functor : ModuleCat R ⥤ ModuleCat S :=
  ModuleCat.extendScalars (algebraMap R S)

/-- Extension of scalars applied termwise to cochain complexes. -/
@[stacks 0G6I "termwise scalar extension for Cech complexes"]
abbrev complexFunctor :
    CochainComplex (ModuleCat R) ℕ ⥤ CochainComplex (ModuleCat S) ℕ :=
  (functor (R := R) (S := S)).mapHomologicalComplex (up ℕ)

/-- The image in `S` of a finite family in `R`. -/
@[stacks 0G6I "base-changed principal-localization family"]
abbrev imageFamily (f : Fin r → R) : Fin r → S :=
  fun i ↦ algebraMap R S (f i)

/-- The ring-valued principal-localization family arrow over `R`. -/
@[stacks 0G6I "source principal-localization family arrow"]
abbrev ringArrow (f : Fin r → R) : Arrow (ModuleCat R) :=
  Arrow.mk (ModuleCat.ofHom (LocalizedModule.Away.Cech.familyMap R f))

/-- The ring-valued family arrow after extension of scalars to `S`. -/
@[stacks 0G6I "scalar extension of the principal-localization family arrow"]
abbrev extendedRingArrow (f : Fin r → R) : Arrow (ModuleCat S) :=
  (functor (R := R) (S := S)).mapArrow.obj (ringArrow f)

/-- The principal-localization family arrow of the image family over `S`. -/
@[stacks 0G6I "target principal-localization family arrow"]
abbrev imageRingArrow (f : Fin r → R) : Arrow (ModuleCat S) :=
  Arrow.mk (ModuleCat.ofHom (LocalizedModule.Away.Cech.familyMap S (imageFamily f)))

/-- Extension of scalars applied termwise to cosimplicial modules. -/
@[stacks 0G6I "termwise scalar extension for cosimplicial modules"]
abbrev cosimplicialFunctor :
    CosimplicialObject (ModuleCat R) ⥤ CosimplicialObject (ModuleCat S) :=
  (CosimplicialObject.whiskering (ModuleCat R) (ModuleCat S)).obj
    (functor (R := R) (S := S))

/-- Extending the regular `R`-module to `S` gives the regular `S`-module. -/
@[stacks 0G6I "base change of the regular module"]
noncomputable def ringIso :
    (functor (R := R) (S := S)).obj (ModuleCat.of R R) ≅ ModuleCat.of S S :=
  ModuleCat.ExtendScalars.tensorIso (R := R) (S := S) (ModuleCat.of R R) ≪≫
    (Algebra.TensorProduct.rid R S S).toLinearEquiv.toModuleIso

/-- Extension of scalars commutes explicitly with the finite product of principal
localizations. -/
@[stacks 0G6I "base change of a finite principal-localization product"]
noncomputable def familyLinearEquiv (f : Fin r → R) :
    S ⊗[R] (∀ i : Fin r, Localization.Away (f i)) ≃ₗ[S]
      ∀ i : Fin r, Localization.Away (algebraMap R S (f i)) :=
  TensorProduct.piRight R S S (fun i : Fin r ↦ Localization.Away (f i)) ≪≫ₗ
    LinearEquiv.piCongrRight fun i : Fin r ↦
      (IsLocalization.Away.tensorEquiv S (f i) (Localization.Away (f i))).toLinearEquiv

/-- The scalar extension of the product of principal localizations is the product attached to
the image family. -/
@[stacks 0G6I "bundled base change of a principal-localization product"]
noncomputable def familyIso (f : Fin r → R) :
    (functor (R := R) (S := S)).obj
        (ModuleCat.of R (∀ i : Fin r, Localization.Away (f i))) ≅
      ModuleCat.of S (∀ i : Fin r, Localization.Away (algebraMap R S (f i))) :=
  ModuleCat.ExtendScalars.tensorIso (R := R) (S := S)
      (ModuleCat.of R (∀ i : Fin r, Localization.Away (f i))) ≪≫
    (familyLinearEquiv f).toModuleIso

/-- The regular-module and localization-product comparisons form the base-change square for the
principal-localization family map. -/
theorem familyMap_commSq (f : Fin r → R) :
    CommSq (ringIso (R := R) (S := S)).hom
      (extendedRingArrow (R := R) (S := S) f).hom
      (imageRingArrow (R := R) (S := S) f).hom (familyIso f).hom := sorry

/-- The extended ring-valued family arrow is explicitly isomorphic to the family arrow of the
image family. -/
@[stacks 0G6I "base change of the principal-localization family arrow"]
noncomputable def arrowIso (f : Fin r → R) :
    extendedRingArrow (R := R) (S := S) f ≅ imageRingArrow (R := R) (S := S) f :=
  Arrow.isoMk (ringIso (R := R) (S := S)) (familyIso f) (familyMap_commSq f).w

/-- At each simplex, extension of scalars commutes with the wide pushout defining the Cech
conerve. -/
@[stacks 0G6I "simplexwise base change of the Cech conerve"]
noncomputable def conerveComponent (f : Fin r → R) (n : SimplexCategory) :
    (extendedRingArrow (R := R) (S := S) f).cechConerve.obj n ≅
      ((cosimplicialFunctor (R := R) (S := S)).obj
        ((ringArrow (R := R) f).cechConerve)).obj n :=
  (HasColimit.isoOfNatIso
      (WidePushoutShape.diagramIsoWideSpan
        ((WidePushoutShape.wideSpan (ringArrow (R := R) f).left
          (fun _ : Fin (n.len + 1) ↦ (ringArrow (R := R) f).right)
          fun _ ↦ (ringArrow (R := R) f).hom) ⋙ functor (R := R) (S := S)))).symm ≪≫
    (preservesColimitIso (functor (R := R) (S := S))
      (WidePushoutShape.wideSpan (ringArrow (R := R) f).left
        (fun _ : Fin (n.len + 1) ↦ (ringArrow (R := R) f).right)
        fun _ ↦ (ringArrow (R := R) f).hom)).symm

/-- The simplexwise scalar-extension/Cech comparison is natural. -/
theorem conerveComponent_naturality (f : Fin r → R)
    {n n' : SimplexCategory} (α : n ⟶ n') :
    (extendedRingArrow (R := R) (S := S) f).cechConerve.map α ≫
        (conerveComponent f n').hom =
      (conerveComponent f n).hom ≫
        ((cosimplicialFunctor (R := R) (S := S)).obj
          ((ringArrow (R := R) f).cechConerve)).map α := sorry

/-- Extension of scalars of the ring-valued Cech conerve is naturally isomorphic to the
termwise extension of the source conerve. -/
@[stacks 0G6I "base change of the Cech conerve"]
noncomputable def conerveIso (f : Fin r → R) :
    (extendedRingArrow (R := R) (S := S) f).cechConerve ≅
      (cosimplicialFunctor (R := R) (S := S)).obj
        ((ringArrow (R := R) f).cechConerve) :=
  NatIso.ofComponents (conerveComponent f)
    (fun α ↦ conerveComponent_naturality f α)

/-- Extension of scalars commutes with the alternating-coface complex functor. -/
theorem alternatingCofaceMapComplex_comp :
    alternatingCofaceMapComplex (ModuleCat R) ⋙ complexFunctor (R := R) (S := S) =
      cosimplicialFunctor (R := R) (S := S) ⋙
        alternatingCofaceMapComplex (ModuleCat S) := sorry

/-- The ordinary ring-valued alternating Cech complex of the image family is explicitly
isomorphic to the extension of the source complex. -/
@[stacks 0G6I "base change of the alternating Cech complex"]
noncomputable def complexIso (f : Fin r → R) :
    Alternating.complex (imageFamily f) S ≅
      (complexFunctor (R := R) (S := S)).obj (Alternating.complex f R) :=
  (alternatingCofaceMapComplex (ModuleCat S)).mapIso
      (((CategoryTheory.CosimplicialObject.cechConerve :
          Arrow (ModuleCat.{u} S) ⥤ CosimplicialObject (ModuleCat.{u} S)).mapIso
        (arrowIso f).symm) ≪≫ conerveIso f) ≪≫
    (eqToIso
      (Functor.congr_obj (alternatingCofaceMapComplex_comp (R := R) (S := S))
        ((ringArrow (R := R) f).cechConerve))).symm

/-- Degree zero of the target extended complex is the regular `S`-module. -/
theorem extended_X_zero_source (f : Fin r → R) :
    (Alternating.extended (imageFamily (R := R) (S := S) f) S).X 0 =
      ModuleCat.of S S := sorry

/-- Degree zero after scalar extension is the extension of the regular `R`-module. -/
theorem extended_X_zero_target (f : Fin r → R) :
    ((complexFunctor (R := R) (S := S)).obj (Alternating.extended f R)).X 0 =
      (functor (R := R) (S := S)).obj (ModuleCat.of R R) := sorry

/-- Positive degree `n + 1` of the target extended complex is degree `n` of its ordinary
complex. -/
theorem extended_X_succ_source (f : Fin r → R) (n : ℕ) :
    (Alternating.extended (imageFamily (R := R) (S := S) f) S).X (n + 1) =
      (Alternating.complex (imageFamily (R := R) (S := S) f) S).X n := sorry

/-- Positive degree `n + 1` after scalar extension is degree `n` after extending the ordinary
complex. -/
theorem extended_X_succ_target (f : Fin r → R) (n : ℕ) :
    ((complexFunctor (R := R) (S := S)).obj (Alternating.extended f R)).X (n + 1) =
      ((complexFunctor (R := R) (S := S)).obj (Alternating.complex f R)).X n := sorry

/-- The explicit degreewise ring-valued base-change comparison. -/
@[stacks 0G6I "degreewise base change of the extended Cech complex"]
noncomputable def ringComponentIso (f : Fin r → R) (i : ℕ) :
    (Alternating.extended (imageFamily (R := R) (S := S) f) S).X i ≅
      ((complexFunctor (R := R) (S := S)).obj (Alternating.extended f R)).X i :=
  match i with
  | 0 =>
      eqToIso (extended_X_zero_source f) ≪≫ (ringIso (R := R) (S := S)).symm ≪≫
        eqToIso (extended_X_zero_target f).symm
  | n + 1 =>
      eqToIso (extended_X_succ_source f n) ≪≫
        (HomologicalComplex.eval (ModuleCat S) (up ℕ) n).mapIso (complexIso f) ≪≫
        eqToIso (extended_X_succ_target f n).symm

/-- The degreewise ring-valued base-change comparisons commute with the differentials. -/
theorem ringComponentIso_comm (f : Fin r → R)
    (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
    (ringComponentIso f i).hom ≫
        ((complexFunctor (R := R) (S := S)).obj (Alternating.extended f R)).d i j =
      (Alternating.extended (imageFamily f) S).d i j ≫ (ringComponentIso f j).hom := sorry

/-- The ring-valued extended alternating Cech complex commutes with extension of scalars. -/
@[stacks 0G6I "base change of the ring-valued extended Cech complex"]
noncomputable def ringExtendedIso (f : Fin r → R) :
    Alternating.extended (imageFamily (R := R) (S := S) f) S ≅
      (complexFunctor (R := R) (S := S)).obj (Alternating.extended f R) :=
  HomologicalComplex.Hom.isoOfComponents (ringComponentIso f) (ringComponentIso_comm f)

/-- Tensoring after termwise scalar extension is the complex associated to the composite
module functor. -/
@[stacks 0G6I "tensor after termwise scalar extension"]
noncomputable def tensorExtendScalarsComplexIso
    (M : Type u) [AddCommGroup M] [Module R M]
    (K : CochainComplex (ModuleCat R) ℕ) :
    ((tensorLeft ((functor (R := R) (S := S)).obj (ModuleCat.of R M))).mapHomologicalComplex
        (up ℕ)).obj ((complexFunctor (R := R) (S := S)).obj K) ≅
      (((functor (R := R) (S := S)) ⋙
        tensorLeft ((functor (R := R) (S := S)).obj (ModuleCat.of R M))).mapHomologicalComplex
          (up ℕ)).obj K :=
  eqToIso rfl

/-- Extending the tensor-by-`M` complex is the complex associated to the composite module
functor. -/
@[stacks 0G6I "scalar extension of a tensor complex"]
noncomputable def extendScalarsTensorComplexIso
    (M : Type u) [AddCommGroup M] [Module R M]
    (K : CochainComplex (ModuleCat R) ℕ) :
    ((tensorLeft (ModuleCat.of R M) ⋙ functor (R := R) (S := S)).mapHomologicalComplex
        (up ℕ)).obj K ≅
      (complexFunctor (R := R) (S := S)).obj
        (((tensorLeft (ModuleCat.of R M)).mapHomologicalComplex (up ℕ)).obj K) :=
  eqToIso rfl

/-- Rebracketing comparison between tensoring an extended complex by `S ⊗[R] M` and extending
the tensor-by-`M` complex. -/
@[stacks 0G6I "tensor and scalar-extension reassociation for Cech complexes"]
noncomputable def tensorReassociationIso
    (M : Type u) [AddCommGroup M] [Module R M]
    (K : CochainComplex (ModuleCat R) ℕ) :
    ((tensorLeft (ModuleCat.of S (S ⊗[R] M))).mapHomologicalComplex (up ℕ)).obj
        ((complexFunctor (R := R) (S := S)).obj K) ≅
      (complexFunctor (R := R) (S := S)).obj
        (((tensorLeft (ModuleCat.of R M)).mapHomologicalComplex (up ℕ)).obj K) :=
  let extendedM := (functor (R := R) (S := S)).obj (ModuleCat.of R M)
  let tensorLeftModuleIso : tensorLeft extendedM ≅ tensorLeft (ModuleCat.of S (S ⊗[R] M)) :=
    (tensoringLeft (ModuleCat S)).mapIso
      (ModuleCat.ExtendScalars.tensorIso (R := R) (S := S) (ModuleCat.of R M))
  let tensorCommIso :
      tensorLeft (ModuleCat.of R M) ⋙ functor (R := R) (S := S) ≅
        functor (R := R) (S := S) ⋙ tensorLeft extendedM :=
    ModuleCat.ExtendScalars.tensorLeftIso (algebraMap R S) (ModuleCat.of R M)
  let tensorCommComplexIso :
      (((functor (R := R) (S := S)) ⋙ tensorLeft extendedM).mapHomologicalComplex
          (up ℕ)).obj K ≅
        ((tensorLeft (ModuleCat.of R M) ⋙ functor (R := R) (S := S)).mapHomologicalComplex
          (up ℕ)).obj K :=
    ((NatIso.mapHomologicalComplex tensorCommIso (up ℕ)).app K).symm
  ((NatIso.mapHomologicalComplex tensorLeftModuleIso (up ℕ)).app
      ((complexFunctor (R := R) (S := S)).obj K)).symm ≪≫
    tensorExtendScalarsComplexIso M K ≪≫
    tensorCommComplexIso ≪≫
    extendScalarsTensorComplexIso M K

/-- Lemma 15.29.3: the extended alternating Cech complex of the image family with coefficients
`S ⊗[R] M` is canonically the scalar extension of the source extended complex. -/
@[stacks 0G6I "Lemma 15.29.3"]
noncomputable def extendedIso
    (f : Fin r → R) (M : Type u) [AddCommGroup M] [Module R M] :
    Alternating.extended (imageFamily f) (S ⊗[R] M) ≅
      (complexFunctor (R := R) (S := S)).obj (Alternating.extended f M) :=
  let ringCech := Alternating.extended f R
  let tensorS :=
    ((tensorLeft (ModuleCat.of S (S ⊗[R] M))).mapHomologicalComplex (up ℕ) :
      CochainComplex (ModuleCat S) ℕ ⥤ CochainComplex (ModuleCat S) ℕ)
  Tensor.extendedIso (imageFamily f) (S ⊗[R] M) ≪≫
    tensorS.mapIso (ringExtendedIso f) ≪≫
    tensorReassociationIso M ringCech ≪≫
    ((complexFunctor (R := R) (S := S)).mapIso (Tensor.extendedIso f M)).symm

end LocalizedModule.Away.Cech.Alternating.BaseChange
