module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Differentials.Field
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Inversion
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Transitivity
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Differentials

/-!
# Smoothness of groupoid schemes

Smoothness criteria for the source and target maps of a groupoid scheme over the spectrum of
a field.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The target map of a groupoid scheme over the spectrum of a perfect field is smooth when
both structure maps are locally of finite type and the arrow scheme is reduced. -/
theorem targetSmoothOfPerfectFieldOfIsReduced
    {S : Scheme.{u}} (G : GroupoidScheme S) {k : Type u} [Field k] [PerfectField k]
    (eU : Spec (CommRingCat.of k) ≅ G.U.left)
    [LocallyOfFiniteType G.s.left] [LocallyOfFiniteType G.t.left] [IsReduced G.R.left] :
    Smooth G.t.left := sorry

/-- The source map of a groupoid scheme over the spectrum of a perfect field is smooth when
both structure maps are locally of finite type and the arrow scheme is reduced. -/
theorem sourceSmoothOfPerfectFieldOfIsReduced
    {S : Scheme.{u}} (G : GroupoidScheme S) {k : Type u} [Field k] [PerfectField k]
    (eU : Spec (CommRingCat.of k) ≅ G.U.left)
    [LocallyOfFiniteType G.s.left] [LocallyOfFiniteType G.t.left] [IsReduced G.R.left] :
    Smooth G.s.left := sorry

/-- Groupoid inversion exchanges smoothness of the source and target maps. -/
theorem sourceSmooth_iff_targetSmooth {S : Scheme.{u}} (G : GroupoidScheme S) :
    Smooth G.s.left ↔ Smooth G.t.left :=
  sourceProperty_iff_targetProperty G (@Smooth)

/-- The target map of a groupoid scheme over the spectrum of a characteristic-zero field is
smooth when both endpoint maps are locally of finite type. -/
theorem targetSmoothOfCharZero {S : Scheme.{u}} (G : GroupoidScheme S)
    {k : Type u} [Field k] [CharZero k]
    (eU : Spec (CommRingCat.of k) ≅ G.U.left)
    [LocallyOfFiniteType G.s.left] [LocallyOfFiniteType G.t.left] :
    Smooth G.t.left := by
  have hFree : SheafOfModules.IsFree Ω[G.t.left.toShHom] :=
    targetDifferentials_isFreeOfSpecField G eU
  have hLocallyFree : (Ω[G.t.left.toShHom]).IsLocallyFree := by
    -- Local instance justification (proof-local temporary data): freeness is installed only to
    -- obtain local freeness of the target-relative differential sheaf.
    let _ : SheafOfModules.IsFree Ω[G.t.left.toShHom] := hFree
    rcases SheafOfModules.IsFree.exists_iso_free
        (F := Ω[G.t.left.toShHom]) with ⟨I, ⟨e⟩⟩
    exact SheafOfModules.IsLocallyFree.of_iso e.symm
  have hToSpecLocallyFree :
      (Ω[(G.t.left ≫ eU.inv).toShHom]).IsLocallyFree := by
    -- Local instance justification (proof-local temporary data): the target map is viewed over
    -- the object scheme only while applying relative-differentials transitivity.
    let _ : G.R.left.Over G.U.left := ⟨G.t.left⟩
    -- Local instance justification (proof-local temporary data): the inverse object isomorphism
    -- is viewed as a structure map only for the transitivity comparison.
    let _ : G.U.left.Over (Spec (CommRingCat.of k)) := ⟨eU.inv⟩
    -- Local instance justification (proof-local temporary data): the composite structure map is
    -- installed only for the transitivity comparison.
    let _ : G.R.left.Over (Spec (CommRingCat.of k)) := ⟨G.t.left ≫ eU.inv⟩
    -- Local instance justification (defeq pin): the explicit composite equality fixes the
    -- transitivity tower used by the canonical projection.
    let _ : CategoryTheory.IsOverTower G.R.left G.U.left
        (Spec (CommRingCat.of k)) := ⟨rfl⟩
    -- Local instance justification (proof-local temporary data): the base isomorphism is a
    -- thickening only to make the transitivity projection invertible.
    let _ : IsThickening (G.U.left ↘ Spec (CommRingCat.of k)) := by
      change IsThickening eU.inv
      infer_instance
    let hIso : IsIso
        (Scheme.RelativeDifferentials.Transitivity.projection
          G.R.left G.U.left (Spec (CommRingCat.of k))) := inferInstance
    let e : Ω[(G.t.left ≫ eU.inv).toShHom] ≅ Ω[G.t.left.toShHom] :=
      @asIso _ _ _ _
        (Scheme.RelativeDifferentials.Transitivity.projection
          G.R.left G.U.left (Spec (CommRingCat.of k))) hIso
    exact SheafOfModules.IsLocallyFree.of_iso e.symm
  -- Local instance justification (proof-local temporary data): finite type of the composite is
  -- installed only for the characteristic-zero differential criterion.
  let _ : LocallyOfFiniteType (G.t.left ≫ eU.inv) := by
    infer_instance
  -- Local instance justification (proof-local temporary data): local freeness of the composite
  -- differential sheaf is installed only for the characteristic-zero differential criterion.
  let _ : (Ω[(G.t.left ≫ eU.inv).toShHom]).IsLocallyFree := hToSpecLocallyFree
  have hTargetToSpec : Smooth (G.t.left ≫ eU.inv) := by
    infer_instance
  have hPost : Smooth ((G.t.left ≫ eU.inv) ≫ eU.hom) :=
    MorphismProperty.RespectsIso.postcomp
      (@Smooth) eU.hom (G.t.left ≫ eU.inv) hTargetToSpec
  simpa [Category.assoc] using hPost

/-- The source map of a groupoid scheme over the spectrum of a characteristic-zero field is
smooth when both endpoint maps are locally of finite type. -/
theorem sourceSmoothOfCharZero {S : Scheme.{u}} (G : GroupoidScheme S)
    {k : Type u} [Field k] [CharZero k]
    (eU : Spec (CommRingCat.of k) ≅ G.U.left)
    [LocallyOfFiniteType G.s.left] [LocallyOfFiniteType G.t.left] :
    Smooth G.s.left :=
  (sourceSmooth_iff_targetSmooth G).2 (targetSmoothOfCharZero G eU)

end AlgebraicGeometry.GroupoidScheme
