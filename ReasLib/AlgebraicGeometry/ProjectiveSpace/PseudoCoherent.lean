module

public import Mathlib.Data.List.TFAE
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.RHom
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.FlatPullbackSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Tensor

/-!
# Pseudo-coherent complexes on projective space

Pseudo-coherence of a quasicoherent derived module on standard projective space can be detected
by derived global sections after tensoring with pseudo-coherent objects, perfect objects, or a
finite range of twists, and equivalently by derived Hom from perfect objects.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- For a quasicoherent derived module on standard projective space, pseudo-coherence is
equivalent to the pseudo-coherence of tensor global sections against every pseudo-coherent
object, against every perfect object, of derived Hom from every perfect object, and of tensor
global sections against the twists of degrees from zero through the dimension. -/
theorem pseudoCoherent_tfae
    (A : Type u) [CommRing A] (n : ℕ)
    (K : Scheme.ModuleDerived.Quasicoherent (scheme A n)) :
    List.TFAE [
      RingedSpace.ModuleDerived.IsPseudoCoherent K.obj,
      ∀ E : RingedSpace.ModuleDerived (scheme A n).toRingedSpace,
        RingedSpace.ModuleDerived.IsPseudoCoherent E →
          DerivedCategory.IsPseudoCoherent
            ((Scheme.FlatPullbackSections.baseSections (toSpec A n)).obj (E ⊗ᴸ K.obj)),
      ∀ E : RingedSpace.ModuleDerived (scheme A n).toRingedSpace,
        RingedSpace.ModuleDerived.IsPerfect E →
          DerivedCategory.IsPseudoCoherent
            ((Scheme.FlatPullbackSections.baseSections (toSpec A n)).obj (E ⊗ᴸ K.obj)),
      ∀ E : RingedSpace.ModuleDerived (scheme A n).toRingedSpace,
        RingedSpace.ModuleDerived.IsPerfect E →
          DerivedCategory.IsPseudoCoherent (rHom A n E K.obj),
      ∀ d : Fin (n + 1),
        DerivedCategory.IsPseudoCoherent
          ((Scheme.FlatPullbackSections.baseSections (toSpec A n)).obj
            (K.obj ⊗ᴸ (DerivedCategory.singleFunctor (scheme A n).Modules 0).obj
              (twistingSheaf A n (d : ℤ))))
    ] := sorry

/-- A quasicoherent derived module on standard projective space is pseudo-coherent exactly when
tensoring it with every pseudo-coherent derived module has pseudo-coherent derived global
sections over the base ring. -/
theorem isPseudoCoherent_iff_tensor_pseudoCoherent
    (A : Type u) [CommRing A] (n : ℕ)
    (K : Scheme.ModuleDerived.Quasicoherent (scheme A n)) :
    RingedSpace.ModuleDerived.IsPseudoCoherent K.obj ↔
      ∀ E : RingedSpace.ModuleDerived (scheme A n).toRingedSpace,
        RingedSpace.ModuleDerived.IsPseudoCoherent E →
          DerivedCategory.IsPseudoCoherent
            ((Scheme.FlatPullbackSections.baseSections (toSpec A n)).obj (E ⊗ᴸ K.obj)) := sorry

/-- A quasicoherent derived module on standard projective space is pseudo-coherent exactly when
tensoring it with every perfect derived module has pseudo-coherent derived global sections over
the base ring. -/
theorem isPseudoCoherent_iff_tensor_perfect
    (A : Type u) [CommRing A] (n : ℕ)
    (K : Scheme.ModuleDerived.Quasicoherent (scheme A n)) :
    RingedSpace.ModuleDerived.IsPseudoCoherent K.obj ↔
      ∀ E : RingedSpace.ModuleDerived (scheme A n).toRingedSpace,
        RingedSpace.ModuleDerived.IsPerfect E →
          DerivedCategory.IsPseudoCoherent
            ((Scheme.FlatPullbackSections.baseSections (toSpec A n)).obj (E ⊗ᴸ K.obj)) := sorry

/-- A quasicoherent derived module on standard projective space is pseudo-coherent exactly when
its derived Hom from every perfect derived module is pseudo-coherent over the base ring. -/
theorem isPseudoCoherent_iff_rHom_perfect
    (A : Type u) [CommRing A] (n : ℕ)
    (K : Scheme.ModuleDerived.Quasicoherent (scheme A n)) :
    RingedSpace.ModuleDerived.IsPseudoCoherent K.obj ↔
      ∀ E : RingedSpace.ModuleDerived (scheme A n).toRingedSpace,
        RingedSpace.ModuleDerived.IsPerfect E →
          DerivedCategory.IsPseudoCoherent (rHom A n E K.obj) := sorry

/-- A quasicoherent derived module on standard projective `n`-space is pseudo-coherent exactly
when its tensor products with the twists of degrees zero through `n` have pseudo-coherent derived
global sections over the base ring. -/
theorem isPseudoCoherent_iff_twists
    (A : Type u) [CommRing A] (n : ℕ)
    (K : Scheme.ModuleDerived.Quasicoherent (scheme A n)) :
    RingedSpace.ModuleDerived.IsPseudoCoherent K.obj ↔
      ∀ d : Fin (n + 1),
        DerivedCategory.IsPseudoCoherent
          ((Scheme.FlatPullbackSections.baseSections (toSpec A n)).obj
            (K.obj ⊗ᴸ (DerivedCategory.singleFunctor (scheme A n).Modules 0).obj
              (twistingSheaf A n (d : ℤ)))) := sorry

end AlgebraicGeometry.ProjectiveSpace

end
