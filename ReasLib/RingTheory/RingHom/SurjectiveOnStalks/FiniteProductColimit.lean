/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.SurjectiveOnStalks

/-!
# Surjectivity on stalks for finite-product colimits

This file proves that the structure map of a directed colimit of finite products of a field is
surjective on stalks.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace RingHom

/-- The algebra map into a directed colimit of finite function algebras over a field is
surjective on stalks. -/
theorem algebraMap_surjectiveOnStalks_of_finitePiColimit
    {k : Type u} [Field k]
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommAlgCat.{u} k) (c : Cocone F) (hc : IsColimit c)
    (ι : I → Type u) [∀ i, _root_.Finite (ι i)]
    (e : ∀ i, F.obj i ≅ CommAlgCat.of k (ι i → k)) :
    SurjectiveOnStalks (algebraMap k c.pt) := by
  rw [surjectiveOnStalks_iff_forall_maximal']
  intro J hJ s
  -- Local instance justification (proof-local temporary data): IsFiltered is introduced only to transport the supplied colimit through forgetful functors.
  letI : IsFiltered I := ⟨⟩
  let E : CommAlgCat k ⥤ Under (CommRingCat.of k) :=
    (commAlgCatEquivUnder (CommRingCat.of k)).functor
  -- Local instance justification (proof-local temporary data): this preservation instance is used only to transport the supplied cocone in the proof.
  letI : PreservesColimit F E := by
    dsimp [E]
    infer_instance
  let cUnder : Cocone (F ⋙ E ⋙ Under.forget (CommRingCat.of k)) :=
    (Under.forget (CommRingCat.of k)).mapCocone (E.mapCocone c)
  have hcUnder : IsColimit cUnder := by
    exact isColimitOfPreserves (Under.forget (CommRingCat.of k)) <|
      isColimitOfPreserves E hc
  obtain ⟨j, y, hy⟩ := Concrete.isColimit_exists_rep (F ⋙ E ⋙ Under.forget (CommRingCat.of k))
    hcUnder (show ToType cUnder.pt from s)
  change F.obj j at y
  change (c.ι.app j).hom y = s at hy
  let ϕ : F.obj j ⟶ c.pt := c.ι.app j
  have hyϕ : ϕ.hom y = s := by
    change ((c.ι.app j).hom y : c.pt) = s
    simpa [ϕ, Functor.const_obj_obj] using hy
  let p : PrimeSpectrum (F.obj j) :=
    PrimeSpectrum.comap (c.ι.app j).hom.toRingHom ⟨J, hJ.isPrime⟩
  let pPi : PrimeSpectrum (ι j → k) :=
    PrimeSpectrum.comap (e j).inv.hom p
  obtain ⟨a, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq pPi
  -- Local instance justification (proof-local temporary data): decidable equality is used only to form the selected Pi.single coordinate in this proof.
  letI : DecidableEq (ι j) := Classical.decEq _
  refine ⟨((e j).hom y) a, 1, (c.ι.app j) ((e j).inv.hom (Pi.single a 1)), ?_, ?_, ?_⟩
  · intro hd
    have hp_stage : (e j).inv.hom (Pi.single a 1) ∈ p.asIdeal := hd
    have hp_pi : Pi.single a 1 ∈ pPi.asIdeal := hp_stage
    rw [← hq] at hp_pi
    have hq_one : (1 : k) ∈ q.asIdeal := by
      simpa using hp_pi
    exact q.2.ne_top (q.asIdeal.eq_top_of_isUnit_mem hq_one isUnit_one)
  · simpa using J.ne_top_iff_one.mp hJ.ne_top
  · simp only [map_one]
    have hstage :
        ((e j).inv.hom (Pi.single a 1)) * y =
          ((e j).inv.hom (Pi.single a 1)) * algebraMap k (F.obj j) (((e j).hom y) a) := by
      let ej : F.obj j ≃ₐ[k] (ι j → k) := CommAlgCat.algEquivOfIso (e j)
      apply ej.injective
      ext b
      change ((e j).hom (((e j).inv.hom (Pi.single a 1)) * y) b) =
          ((e j).hom (((e j).inv.hom (Pi.single a 1)) *
            algebraMap k (F.obj j) ((e j).hom y a)) b)
      rw [map_mul, map_mul]
      by_cases hb : b = a
      · subst hb
        simp [AlgHom.commutes]
      · simp [AlgHom.commutes, hb]
    have himage :
        (ϕ.hom (((e j).inv.hom (Pi.single a 1)) * y) : c.pt) =
          (ϕ.hom
            (((e j).inv.hom (Pi.single a 1)) * algebraMap k (F.obj j) ((e j).hom y a)) : c.pt) := by
      exact congrArg (fun z ↦ (ϕ.hom z : c.pt)) hstage
    let z : c.pt := (c.ι.app j).hom ((e j).inv.hom (Pi.single a 1))
    have himage' : z * s = z * algebraMap k c.pt ((e j).hom y a) := by
      calc
        z * s = z * ϕ.hom y := by rw [hyϕ]
        _ = ϕ.hom (((e j).inv.hom (Pi.single a 1)) * y) := by
          dsimp [z, ϕ]
          rw [map_mul]
          rfl
        _ = ϕ.hom (((e j).inv.hom (Pi.single a 1)) *
            algebraMap k (F.obj j) ((e j).hom y a)) := himage
        _ = z * algebraMap k c.pt ((e j).hom y a) := by
          dsimp [z, ϕ]
          rw [map_mul, AlgHom.commutes]
          rfl
    simpa [z] using himage'

end RingHom
