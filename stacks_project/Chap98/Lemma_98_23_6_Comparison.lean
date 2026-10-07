module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Composition
public import stacks_project.Chap98.Definition_98_23_5_Obstruction

/-!
# Comparison maps along naive obstruction functoriality

The functoriality map `E_x ⟶ Res_A(E_y)` induces, after derived extension of
scalars to a field `k` over `B`, a comparison `E_x ⊗_A^L k ⟶ E_y ⊗_B^L k` in
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
    (k : Type u) [Field k] [Algebra η.carrier k] :
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
    (k : Type u) [Field k] [Algebra η.carrier k] :
    derivedMapAlong 𝒪 f k =
      let σ := f.toRingHom
      let τ := algebraMap η.carrier k
      let Ex := Minus.ι.obj (𝒪.complex ξ)
      let Ey := Minus.ι.obj (𝒪.complex η)
      (ModuleCat.DerivedExtension.Composition.iso σ τ).inv.app Ex ≫
        (ModuleCat.derivedExtensionOfScalars τ).map
          ((ModuleCat.derivedExtensionRestrictionHomEquiv σ Ex Ey).symm
            (𝒪.map f)) :=
  sorry

/-- The degree-`i` homology map of `derivedMapAlong`. -/
def homologyMapAlong (𝒪 : NaiveObstructionTheory X)
    {ξ η : ObjectOverAffineOpen X} (f : ObjectOverAffineOpen.Hom ξ η)
    (k : Type u) [Field k] [Algebra η.carrier k] (i : ℤ) :
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
    (k : Type u) [Field k] [Algebra η.carrier k] (i : ℤ) :
    homologyMapAlong 𝒪 f k i =
      (homologyFunctor (ModuleCat.{u} k) i).map (derivedMapAlong 𝒪 f k) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.NaiveObstructionTheory

