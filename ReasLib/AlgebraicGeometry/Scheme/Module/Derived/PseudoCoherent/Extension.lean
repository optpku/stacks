module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Basic
public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback

@[expose] public section

/-!
# Extending pseudo-coherent derived modules

Pseudo-coherent derived modules on quasi-compact open subschemes of affine schemes admit
bounded-above, termwise finite-free extensions to the ambient scheme.
-/

open AlgebraicGeometry CategoryTheory RingedSpace.Hom.IsFlat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.PseudoCoherent

/-- A pseudo-coherent derived module on a quasi-compact open subscheme of an affine scheme is
the derived restriction of a bounded-above complex of finite-free module sheaves on the ambient
scheme. -/
theorem exists_finiteFree_extension {X U : Scheme.{u}} [IsAffine X]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (E : RingedSpace.ModuleDerived U.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPseudoCoherent E) :
    ∃ (P : CochainComplex (RingedSpace.Modules X.toRingedSpace) ℤ)
      (e : (Scheme.DerivedQCoh.OpenImmersion.exactPullback j).mapDerivedCategory.obj
        (DerivedCategory.Q.obj P) ≅ E),
      CochainComplex.minus (RingedSpace.Modules X.toRingedSpace) P ∧
        ∀ i, SheafOfModules.IsFiniteFree (P.X i) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.PseudoCoherent
