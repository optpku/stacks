module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.OpenImmersion

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.InfinitesimalFiber

/-- The positive infinitesimal fibre of `f` cut out by the `n`th power of the maximal ideal. -/
noncomputable def stage {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (n : ℕ+) : Scheme :=
  pullback f (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R) ^ (n : ℕ)))))

/-- The projection from the positive infinitesimal fibre to the ambient scheme. -/
noncomputable def inclusion {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (n : ℕ+) :
    stage f n ⟶ X :=
  pullback.fst f (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R) ^ (n : ℕ)))))

/-- The structure morphism of the positive infinitesimal fibre to its quotient base. -/
noncomputable def toSpec {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (n : ℕ+) :
    stage f n ⟶ Spec (CommRingCat.of
      (R ⧸ (IsLocalRing.maximalIdeal R) ^ (n : ℕ))) :=
  pullback.snd f (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R) ^ (n : ℕ)))))

/-- The open complement of a closed subset on a positive infinitesimal fibre. -/
noncomputable def openComplement {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (Z : Closeds X) (n : ℕ+) :
    (stage f n).Opens :=
  (inclusion f n ⁻¹ᵁ (Z.compl : X.Opens))

/-- The inverse image of a closed subset on a positive infinitesimal fibre. -/
noncomputable def closedSubset {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (Z : Closeds X) (n : ℕ+) :
    Closeds (stage f n) :=
  Z.preimage (inclusion f n).continuous

/-- The pushforward to `X` of a module on the open complement in the first fibre. -/
noncomputable def pushforwardFromOpen {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (Z : Closeds X)
    (F₁ : (Scheme.Opens.toScheme (openComplement f Z 1)).Modules) : X.Modules :=
  (Scheme.Modules.pushforward (inclusion f 1)).obj
    ((Scheme.Modules.pushforward (Scheme.Opens.ι (openComplement f Z 1))).obj F₁)

/-- The pushforward to `X` of the degree-one higher direct image on the first fibre. -/
noncomputable def higherDirectImageFromOpen {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (Z : Closeds X)
    (F₁ : (Scheme.Opens.toScheme (openComplement f Z 1)).Modules) : X.Modules :=
  (Scheme.Modules.pushforward (inclusion f 1)).obj
    (RingedSpace.Hom.higherDirectImageModule
      (Scheme.Opens.ι (openComplement f Z 1)).toShHom F₁ 1)

/-- The degree-zero direct-image comparison for the first infinitesimal fibre. -/
theorem pushforward_isIsomorphic {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (Z : Closeds X)
    (F₁ : (Scheme.Opens.toScheme (openComplement f Z 1)).Modules) :
    IsIsomorphic
      ((Scheme.Modules.pushforward (Scheme.Opens.ι Z.compl)).obj
        ((Scheme.Modules.pushforward
          (AlgebraicGeometry.morphismRestrict (inclusion f 1) Z.compl)).obj F₁))
      (pushforwardFromOpen f Z F₁) := sorry

/-- The degree-one direct-image comparison for the first infinitesimal fibre. -/
theorem higherDirectImage_isIsomorphic {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (Z : Closeds X)
    (F₁ : (Scheme.Opens.toScheme (openComplement f Z 1)).Modules) :
    IsIsomorphic
      (RingedSpace.Hom.higherDirectImageModule (Scheme.Opens.ι Z.compl).toShHom
        ((Scheme.Modules.pushforward
          (AlgebraicGeometry.morphismRestrict (inclusion f 1) Z.compl)).obj F₁) 1)
      (higherDirectImageFromOpen f Z F₁) := sorry

/-- On a Noetherian ambient scheme, coherence of the degree-zero direct image is detected on the
open first fibre. -/
theorem pushforward_isCoherent_iff {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} [IsNoetherian X] (f : X ⟶ Spec (CommRingCat.of R)) (Z : Closeds X)
    (F₁ : (Scheme.Opens.toScheme (openComplement f Z 1)).Modules) :
    (pushforwardFromOpen f Z F₁).IsCoherent ↔
      ((Scheme.Modules.pushforward (Scheme.Opens.ι (openComplement f Z 1))).obj F₁).IsCoherent := sorry

/-- On a Noetherian ambient scheme, coherence of the degree-one direct image is detected on the
open first fibre. -/
theorem higherDirectImage_isCoherent_iff {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} [IsNoetherian X] (f : X ⟶ Spec (CommRingCat.of R)) (Z : Closeds X)
    (F₁ : (Scheme.Opens.toScheme (openComplement f Z 1)).Modules) :
    (higherDirectImageFromOpen f Z F₁).IsCoherent ↔
      (RingedSpace.Hom.higherDirectImageModule
        (Scheme.Opens.ι (openComplement f Z 1)).toShHom F₁ 1).IsCoherent := sorry

end AlgebraicGeometry.Scheme.InfinitesimalFiber
