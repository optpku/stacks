module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.InjectiveHull
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 58.29.1: for a regular local ring containing a field, an étale quasi-compact
morphism avoiding the closed point and affine over the punctured spectrum has positive-degree
structure-sheaf cohomology isomorphic to a direct sum of copies of an injective hull of the
residue field. -/
@[stacks 0ECB] #check (AlgebraicGeometry.Scheme.Hom.cohomology_isDirectSum_injectiveHull :
  ∀
    {k A : Type u} [Field k] [CommRing A] [Algebra k A] [IsRegularLocalRing A]
    {V : Scheme.{u}} (f : V ⟶ Spec (CommRingCat.of A)) [Etale f] [QuasiCompact f]
    (h_m : IsLocalRing.closedPoint A ∉ Set.range f)
    (g : V ⟶ PuncturedSpectrum.scheme A) [IsAffineHom g]
    (h_factor : g ≫ (PuncturedSpectrum.puncturedOpen A).ι = f)
    {E : Type u} [AddCommGroup E] [Module A E] [Module.Injective A E]
    (ιE : IsLocalRing.ResidueField A →ₗ[A] E) (hι : ιE.IsInjectiveHull),
    ∀ i : ℕ, 0 < i →
      ∃ J : Type u,
        Nonempty
          (Scheme.Hom.cohomology f (SheafOfModules.unit V.ringCatSheaf : V.Modules) i ≅
            ModuleCat.of A (DirectSum J (fun _ ↦ E))))
