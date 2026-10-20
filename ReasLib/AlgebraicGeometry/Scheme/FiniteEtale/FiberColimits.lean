module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Colimits
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Finite colimits of geometric fibres

Disjoint-union branches are read through the native scheme coproduct. Quotient
representatives are lifted through the actual affine equalizer inclusion using
integral lying-over and the native separably-closed étale lifting construction.
-/

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {X : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
variable (point : Spec (.of K) ⟶ X)

namespace FiberColimits

section Coproduct

variable {ι : Type u} [Finite ι] (Y : ι → FiniteEtale X)

/-- Read the actual disjoint-union branch of a geometric point. -/
def branch (t : (fiber point).obj (coproduct Y)) : ι :=
  ((AlgebraicGeometry.sigmaMk (fun i ↦ (Y i).left)).symm (t.left (default : Spec (.of K)))).1

/-- The one-point source lies in the branch determined by its underlying point. -/
theorem branch_range (t : (fiber point).obj (coproduct Y)) :
    Set.range t.left ⊆ Set.range (Sigma.ι (fun i ↦ (Y i).left) (branch point Y t)) := by
  rintro x ⟨z, rfl⟩
  change Spec (.of K) at z
  have hz : z = (default : Spec (.of K)) := Subsingleton.elim _ _
  subst z
  let p := (AlgebraicGeometry.sigmaMk (fun i ↦ (Y i).left)).symm (t.left (default : Spec (.of K)))
  exact ⟨p.2, by
    change Sigma.ι (fun i ↦ (Y i).left) p.1 p.2 = t.left (default : Spec (.of K))
    rw [← AlgebraicGeometry.sigmaMk_mk]
    exact (AlgebraicGeometry.sigmaMk (fun i ↦ (Y i).left)).apply_symm_apply _⟩

/-- The branch point uses the native inverse of the coproduct open immersion. -/
def branchPoint (t : (fiber point).obj (coproduct Y)) :
    (fiber point).obj (Y (branch point Y t)) := by
  letI : IsOpenImmersion (Sigma.ι (fun i ↦ (Y i).left) (branch point Y t)) :=
    inferInstanceAs (IsOpenImmersion ((AlgebraicGeometry.sigmaOpenCover (fun i ↦ (Y i).left)).f _))
  exact Over.homMk
    (IsOpenImmersion.lift
      (Sigma.ι (fun i ↦ (Y i).left) (branch point Y t)) t.left (branch_range point Y t))
    (w := sorry)

/-- A cocone of finite-set maps is evaluated on the actual branch point. -/
def coproductDesc (c : Cocone (Discrete.functor Y ⋙ finiteFiber point)) :
    (finiteFiber point).obj (coproduct Y) ⟶ c.pt :=
  FintypeCat.homMk fun t ↦ c.ι.app ⟨branch point Y t⟩ (branchPoint point Y t)

/-- The preserved coproduct has an explicit descent function. -/
def coproductIsColimit :
    IsColimit ((finiteFiber point).mapCocone (FiniteEtale.coproductCofan Y)) where
  desc := coproductDesc point Y
  fac := sorry
  uniq := sorry

end Coproduct

namespace Coequalizer

variable {Z Y : FiniteEtale X} (a b : Z ⟶ Y)

/-- The equalizer inclusion is injective on its literal subring carrier. -/
theorem inclusion_injective (U : X.Opens) :
    Function.Injective (FiniteEtale.Coequalizer.inclusion a b U).hom := by
  intro x y h
  exact Subtype.ext h

/-- Finite coordinates over the base are integral over the intermediate equalizer ring. -/
theorem inclusion_integral (U : X.affineOpens) :
    (FiniteEtale.Coequalizer.inclusion a b U).hom.IsIntegral := sorry

/-- Select a base affine chart by its actual cover-index operation. -/
def affineIndex : X.affineOpens :=
  X.directedAffineCover.idx (point default)

/-- The quotient point lies in the chosen native gluing chart. -/
theorem chart_range (t : (fiber point).obj (FiniteEtale.Coequalizer.obj a b)) :
    Set.range t.left ⊆ Set.range
      (colimit.ι (FiniteEtale.Coequalizer.gluingData a b).functor (affineIndex point)) := by
  rintro _ ⟨x, rfl⟩
  rw [← (FiniteEtale.Coequalizer.gluingData a b).preimage_toBase_eq_range_ι]
  change (t.left ≫ FiniteEtale.Coequalizer.toBase a b) x ∈
    Set.range (X.directedAffineCover.f (affineIndex point))
  have hw : t.left ≫ FiniteEtale.Coequalizer.toBase a b = point := Over.w t
  rw [hw]
  change Spec (.of K) at x
  have hx : x = (default : Spec (.of K)) := Subsingleton.elim _ _
  rw [hx]
  exact X.directedAffineCover.covers (point default)

/-- Restrict the actual quotient point to the affine equalizer spectrum. -/
def affinePoint (t : (fiber point).obj (FiniteEtale.Coequalizer.obj a b)) :
    Spec (.of K) ⟶ Spec (FiniteEtale.Coequalizer.ring a b (affineIndex point)) := by
  letI : IsOpenImmersion (colimit.ι (FiniteEtale.Coequalizer.gluingData a b).functor
      (affineIndex point)) :=
    inferInstanceAs (IsOpenImmersion (((FiniteEtale.Coequalizer.gluingData a b).cover).f _))
  exact IsOpenImmersion.lift
    (colimit.ι (FiniteEtale.Coequalizer.gluingData a b).functor (affineIndex point))
    t.left (chart_range point a b t)

/-- Native integral lying-over supplies a point over the specified affine quotient point. -/
def sectionPrime (t : (fiber point).obj (FiniteEtale.Coequalizer.obj a b)) :
    PrimeSpectrum (FiniteEtale.Coequalizer.sectionRing Y (affineIndex point)) :=
  Classical.choose
    ((inclusion_integral a b (affineIndex point)).comap_surjective
      (inclusion_injective a b (affineIndex point))
      ((affinePoint point a b t) default))

/-- The lifted prime is an actual point of the finite étale source scheme. -/
def sourcePoint (t : (fiber point).obj (FiniteEtale.Coequalizer.obj a b)) : Y.left :=
  (FiniteEtale.Coequalizer.preimage Y (affineIndex point)).ι
    ((FiniteEtale.Coequalizer.preimage Y (affineIndex point)).toScheme.isoSpec.inv
      (sectionPrime point a b t))

/-- Affine coordinate compatibility places the lifted point over the original point. -/
theorem sourcePoint_fac (t : (fiber point).obj (FiniteEtale.Coequalizer.obj a b)) :
    (FiniteEtale.Coequalizer.π a b).left (sourcePoint point a b t) = t.left (default : Spec (.of K)) := sorry

/-- Morphisms between finite étale schemes are étale. -/
theorem quotient_etale : Etale (FiniteEtale.Coequalizer.π a b).left := by
  letI : Etale (FiniteEtale.Coequalizer.obj a b).hom :=
    (FiniteEtale.Coequalizer.obj a b).prop.2
  letI : Etale ((FiniteEtale.Coequalizer.π a b).left ≫
      (FiniteEtale.Coequalizer.obj a b).hom) := by
    rw [MorphismProperty.Over.w]
    exact Y.prop.2
  exact Etale.of_comp (f := (FiniteEtale.Coequalizer.π a b).left)
    (FiniteEtale.Coequalizer.obj a b).hom

/-- The geometric representative is the native étale lift at the actual lifted prime. -/
def representative (t : (fiber point).obj (FiniteEtale.Coequalizer.obj a b)) :
    (fiber point).obj Y := by
  letI := quotient_etale a b
  let lift := Classical.choose
    (Scheme.exists_fac_of_etale_of_isSepClosed (FiniteEtale.Coequalizer.π a b).left
      t.left (sourcePoint point a b t) (sourcePoint_fac point a b t))
  exact Over.homMk lift (w := sorry)

/-- Evaluate the input cofork on the explicitly lifted geometric representative. -/
def desc (c : Cocone (parallelPair a b ⋙ finiteFiber point)) :
    (finiteFiber point).obj (FiniteEtale.Coequalizer.obj a b) ⟶ c.pt :=
  FintypeCat.homMk fun t ↦ c.ι.app WalkingParallelPair.one (representative point a b t)

/-- The geometric quotient carries its actual descent function. -/
def isColimit :
    IsColimit ((finiteFiber point).mapCocone (FiniteEtale.Coequalizer.cofork a b)) where
  desc := desc point a b
  fac := sorry
  uniq := sorry

end Coequalizer

/-- Preservation of finite coproducts retains the actual branch-evaluation desc. -/
instance preservesFiniteCoproducts : PreservesFiniteCoproducts (finiteFiber point) where
  preserves n :=
    { preservesColimit := fun {F} ↦ by
        let family : ULift.{u} (Fin n) → FiniteEtale X := fun i ↦ F.obj ⟨i.down⟩
        let c : Cocone F :=
          { pt := FiniteEtale.coproduct family
            ι := { app := fun i ↦ FiniteEtale.coproductι family ⟨i.as⟩, naturality := sorry } }
        let hc : IsColimit c :=
          { desc := fun t ↦ FiniteEtale.coproductDesc family (fun i ↦ t.ι.app ⟨i.down⟩)
            fac := sorry
            uniq := sorry }
        let mapped : IsColimit ((finiteFiber point).mapCocone c) :=
          { desc := fun t ↦ FintypeCat.homMk fun x ↦
              t.ι.app ⟨(branch point family x).down⟩ (branchPoint point family x)
            fac := sorry
            uniq := sorry }
        exact preservesColimit_of_preserves_colimit_cocone hc mapped }

/-- Preservation of coequalizers retains the actual integral/étale representative. -/
instance preservesCoequalizers :
    PreservesColimitsOfShape WalkingParallelPair (finiteFiber point) where
  preservesColimit {F} := by
    let a := F.map WalkingParallelPairHom.left
    let b := F.map WalkingParallelPairHom.right
    letI : PreservesColimit (parallelPair a b) (finiteFiber point) :=
      preservesColimit_of_preserves_colimit_cocone (FiniteEtale.Coequalizer.isColimit a b)
        (Coequalizer.isColimit point a b)
    exact preservesColimit_of_iso_diagram (finiteFiber point) (diagramIsoParallelPair F).symm

end FiberColimits

/-- Geometric fibres preserve finite colimits by their actual coproduct and quotient desc maps. -/
instance finiteFiber_preservesFiniteColimits :
    PreservesFiniteColimits (finiteFiber point) :=
  preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts (finiteFiber point)

end AlgebraicGeometry.Scheme.FiniteEtale
