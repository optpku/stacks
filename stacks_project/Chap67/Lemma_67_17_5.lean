module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.SchemeTheoreticDensity.StructureSheaf
import StacksCheckRecall

/-!
# Structure-sheaf characterization of scheme-theoretic density

An open immersion of algebraic spaces is scheme-theoretically dense if and only
if the direct-image structure-sheaf map is a monomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.17.5: Let `S` be a scheme. Let `ι : U ⟶ X` be an open immersion of
algebraic spaces over `S`. Then `U` is scheme-theoretically dense in `X` if and
only if `structureSheafMap ι : 𝒪_X ⟶ ι_* 𝒪_U` is a monomorphism. -/
@[stacks 0836] #check
  (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticallyDense.iff_mono_structureSheafMap :
    ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} (ι : U ⟶ X) [IsOpenImmersion ι],
      IsSchemeTheoreticallyDense ι ↔ Mono (structureSheafMap ι))

#check
  (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticallyDense.of_mono_structureSheafMap :
    ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} {ι : U ⟶ X} [IsOpenImmersion ι],
      Mono (structureSheafMap ι) → IsSchemeTheoreticallyDense ι)

#check
  (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticallyDense.mono_structureSheafMap :
    ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} (ι : U ⟶ X) [IsOpenImmersion ι]
      [IsSchemeTheoreticallyDense ι], Mono (structureSheafMap ι))

#check
  (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticallyDense.iff_idealSheafSubobject_eq_bot :
    ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} (ι : U ⟶ X) [IsOpenImmersion ι],
      IsSchemeTheoreticallyDense ι ↔ Hom.idealSheafSubobject ι = ⊥)

end AlgebraicGeometry.AlgebraicSpace
