module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.RaisedGaloisAction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.FixedInterior

/-!
# Compactly supported geometric cohomology as a Galois module

Extension by zero along a compactification computes compactly supported geometric
cohomology with its pullback Galois action.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {k : Type u} [Field k]

/-- Compactly supported geometric étale cohomology `H_c^i(X_{k̄}, F)` as a
`Gal(k̄/k)`-module, obtained by extending `F` by zero along a compactification. -/
def cohomologyCompactSupportGaloisModule (X : SchemeOverField k)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ) :
    Action AddCommGrpCat.{u + 1} Gal(AlgebraicClosure k/k) :=
  geometricEtaleCohomologyGaloisModule₁ P.obj.right
    ((etaleExtensionByZero (Compactification.Of.ι P) AddCommGrpCat.{u + 1}).obj F) i

/-- The underlying abelian group of compactly supported geometric cohomology. -/
theorem cohomologyCompactSupportGaloisModule_V (X : SchemeOverField k)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ) :
    (cohomologyCompactSupportGaloisModule X P F i).V =
      geometricEtaleCohomology₁ P.obj.right
        ((etaleExtensionByZero (Compactification.Of.ι P) AddCommGrpCat.{u + 1}).obj F) i :=
  rfl

/-- Evaluating the compactly supported Galois module recovers the pullback action. -/
theorem cohomologyCompactSupportGaloisModule_ρ (X : SchemeOverField k)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ)
    (σ : Gal(AlgebraicClosure k/k)) :
    (cohomologyCompactSupportGaloisModule X P F i).ρ σ =
      galoisAction_geometricEtaleCohomology₁ P.obj.right
        ((etaleExtensionByZero (Compactification.Of.ι P) AddCommGrpCat.{u + 1}).obj F) i σ :=
  rfl

/-- Compactly supported geometric cohomology is independent of the compactification, up to
a canonical isomorphism of Galois modules. -/
theorem cohomologyCompactSupportGaloisModule_independent
    (X : SchemeOverField k)
    (P Q : Compactification.Of (Spec (CommRingCat.of k)) X)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ) :
    Nonempty
      (cohomologyCompactSupportGaloisModule X P F i ≅
        cohomologyCompactSupportGaloisModule X Q F i) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
