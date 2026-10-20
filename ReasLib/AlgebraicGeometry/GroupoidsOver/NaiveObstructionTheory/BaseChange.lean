/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Composition
public import ReasLib.AlgebraicGeometry.GroupoidsOver.NaiveObstructionTheory
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison maps along naive obstruction functoriality

The functoriality map `E_x ⟶ Res_A(E_y)` induces, after derived extension of
scalars to a commutative `B`-algebra `k`, a comparison `E_x ⊗_A^L k ⟶ E_y ⊗_B^L k` in
`D(ModuleCat k)` and its homology maps.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open DerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.NaiveObstructionTheory

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {X : GroupoidsOver S} [HasStrongRimSchlessinger X]

/-- The induced map `E_x ⊗_A^L k ⟶ E_y ⊗_B^L k` in `D(ModuleCat k)` obtained
from the functoriality map `E_x ⟶ Res_A(E_y)` by adjunction and derived
extension of scalars along `B → k`. -/
def derivedMapAlong (𝒪 : NaiveObstructionTheory X)
    {ξ η : ObjectOverAffineOpen X} (f : ObjectOverAffineOpen.Hom ξ η)
    (k : Type u) [CommRing k] [Algebra η.carrier k] :
    (ModuleCat.derivedExtensionOfScalars
        ((algebraMap η.carrier k).comp f.toRingHom)).obj
      (Minus.ι.obj (𝒪.complex ξ)) ⟶
    (ModuleCat.derivedExtensionOfScalars (algebraMap η.carrier k)).obj
      (Minus.ι.obj (𝒪.complex η)) :=
  let σ := f.toRingHom
  let τ := algebraMap η.carrier k
  let Ex := Minus.ι.obj (𝒪.complex ξ)
  let Ey := Minus.ι.obj (𝒪.complex η)
  (ModuleCat.DerivedExtension.Composition.iso σ τ).inv.app Ex ≫
    (ModuleCat.derivedExtensionOfScalars τ).map
      ((ModuleCat.derivedExtensionRestrictionHomEquiv σ Ex Ey).symm (𝒪.map f))

/-- `derivedMapAlong` is the adjunct of `𝒪.map f`, transported along the
composition isomorphism for derived extension of scalars. -/
theorem derivedMapAlong_eq (𝒪 : NaiveObstructionTheory X)
    {ξ η : ObjectOverAffineOpen X} (f : ObjectOverAffineOpen.Hom ξ η)
    (k : Type u) [CommRing k] [Algebra η.carrier k] :
    derivedMapAlong 𝒪 f k =
      let σ := f.toRingHom
      let τ := algebraMap η.carrier k
      let Ex := Minus.ι.obj (𝒪.complex ξ)
      let Ey := Minus.ι.obj (𝒪.complex η)
      (ModuleCat.DerivedExtension.Composition.iso σ τ).inv.app Ex ≫
        (ModuleCat.derivedExtensionOfScalars τ).map
          ((ModuleCat.derivedExtensionRestrictionHomEquiv σ Ex Ey).symm
            (𝒪.map f)) :=
  rfl

/-- The degree-`i` homology map of `derivedMapAlong`. -/
def homologyMapAlong (𝒪 : NaiveObstructionTheory X)
    {ξ η : ObjectOverAffineOpen X} (f : ObjectOverAffineOpen.Hom ξ η)
    (k : Type u) [CommRing k] [Algebra η.carrier k] (i : ℤ) :
    (homologyFunctor (ModuleCat.{u} k) i).obj
      ((ModuleCat.derivedExtensionOfScalars
          ((algebraMap η.carrier k).comp f.toRingHom)).obj
        (Minus.ι.obj (𝒪.complex ξ))) ⟶
    (homologyFunctor (ModuleCat.{u} k) i).obj
      ((ModuleCat.derivedExtensionOfScalars (algebraMap η.carrier k)).obj
        (Minus.ι.obj (𝒪.complex η))) :=
  (homologyFunctor (ModuleCat.{u} k) i).map (derivedMapAlong 𝒪 f k)

/-- `homologyMapAlong` is the homology functor applied to `derivedMapAlong`. -/
theorem homologyMapAlong_eq (𝒪 : NaiveObstructionTheory X)
    {ξ η : ObjectOverAffineOpen X} (f : ObjectOverAffineOpen.Hom ξ η)
    (k : Type u) [CommRing k] [Algebra η.carrier k] (i : ℤ) :
    homologyMapAlong 𝒪 f k i =
      (homologyFunctor (ModuleCat.{u} k) i).map (derivedMapAlong 𝒪 f k) :=
  rfl

/-- For a naive obstruction theory, restriction along a ring homomorphism induces
bijective homology comparisons after derived extension to any field algebra
in degrees zero and one. -/
@[stacks 07YT]
theorem homologyMapAlong_bijective (𝒪 : NaiveObstructionTheory X)
    {ξ η : ObjectOverAffineOpen X} (f : ObjectOverAffineOpen.Hom ξ η)
    (k : Type u) [Field k] [Algebra η.carrier k]
    (i : ℤ) (hi : i = 0 ∨ i = 1) :
    Function.Bijective (ModuleCat.Hom.hom (homologyMapAlong 𝒪 f k i)) :=
  sorry


end AlgebraicGeometry.GroupoidsOver.NaiveObstructionTheory
