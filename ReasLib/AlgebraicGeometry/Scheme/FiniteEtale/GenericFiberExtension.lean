/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Galois
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Galois.GaloisObjects

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- A finite étale Galois cover of the generic fibre with a rational point over a section extends
to the total space of a smooth geometrically connected family over an integral normal Noetherian
scheme when the order of its group is invertible on the base. -/
theorem exists_finiteEtaleGalois_of_genericFiber
    {S X : Scheme.{u}} [IsIntegral S] [IsNoetherian S] (hS : S.isNormal)
    {f : X ⟶ S} [Smooth f] [GeometricallyConnected f] (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) {G : Type u} [Group G] [Finite G]
    (Z : Scheme.FiniteEtale (f.fiber (genericPoint S)))
    [GaloisCategory (Scheme.FiniteEtale (f.fiber (genericPoint S)))] [IsGalois Z]
    (eG : Aut Z ≃* G) (hinv : IsUnit (Nat.card G : Γ(S, ⊤)))
    (p : Spec (S.residueField (genericPoint S)) ⟶ Z.left)
    (hp : p ≫ Z.hom ≫ f.fiberι (genericPoint S) =
      S.fromSpecResidueField (genericPoint S) ≫ σ) :
    ∃ (Y : Scheme.FiniteEtale X) (_ : GaloisCategory (Scheme.FiniteEtale X))
      (_ : IsGalois Y) (_ : Aut Y ≃* G),
      Nonempty ((finiteEtaleBaseChange (f.fiberι (genericPoint S))).obj Y ≅ Z) :=
  sorry

/-- A finite étale Galois cover of the generic fibre with a rational point over a section extends
to the total space of a smooth geometrically connected family over an integral normal
quasi-compact quasi-separated scheme when the order of its group is invertible on the base. -/
theorem exists_finiteEtaleGalois_of_genericFiber_qcqs
    {S X : Scheme.{u}} [IsIntegral S] [CompactSpace S] [QuasiSeparatedSpace S]
    (hS : S.isNormal) {f : X ⟶ S} [Smooth f] [QuasiCompact f] [QuasiSeparated f]
    [GeometricallyConnected f] (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    {G : Type u} [Group G] [Finite G]
    (Z : Scheme.FiniteEtale (f.fiber (genericPoint S))) [IsGalois Z]
    (eG : Aut Z ≃* G) (hinv : IsUnit (Nat.card G : Γ(S, ⊤)))
    (p : Spec (S.residueField (genericPoint S)) ⟶ Z.left)
    (hp : p ≫ Z.hom ≫ f.fiberι (genericPoint S) =
      S.fromSpecResidueField (genericPoint S) ≫ σ) :
    ∃ (Y : Scheme.FiniteEtale X) (_ : GaloisCategory (Scheme.FiniteEtale X))
      (_ : IsGalois Y) (_ : Aut Y ≃* G),
      Nonempty ((finiteEtaleBaseChange (f.fiberι (genericPoint S))).obj Y ≅ Z) :=
  sorry

end AlgebraicGeometry.Scheme.FiniteEtale
