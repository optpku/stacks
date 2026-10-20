module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.ClosedImmersion.FiniteType
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSmooth
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigEtale
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSurjective
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffineKernel
public import Mathlib.Data.List.TFAE

/-!
# Closed immersions that are rig-smooth and rig-surjective
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FormalAlgebraicSpace
  AffineFormalAlgebraicSpace CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.ClosedImmersion

/-- Every étale morphism from an affine formal algebraic space to `Y` has
base change `pullback.snd f v` corresponding to a surjection of adic
Noetherian rings whose kernel is killed by some ideal of definition. -/
def etaleAffine_kernelKilled {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y)
    [ClosedImmersion f] : Prop :=
  ∀ {V : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace V] [IsAffine V]
    (v : V ⟶ Y) [Etale v],
    KernelKilledByIdealOfDefinition (pullback.snd f v)

/-- `etaleAffine_kernelKilled f` means that every étale morphism from an
affine formal algebraic space to `Y` has base change corresponding to a
surjection of adic Noetherian rings whose kernel is killed by some ideal of
definition. -/
theorem etaleAffine_kernelKilled_iff {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y)
    [ClosedImmersion f] :
    etaleAffine_kernelKilled f ↔
      ∀ {V : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace V] [IsAffine V]
        (v : V ⟶ Y) [Etale v],
        KernelKilledByIdealOfDefinition (pullback.snd f v) :=
  Iff.rfl

/-- For a closed immersion of locally Noetherian formal algebraic spaces,
rig-smoothness and rig-surjectivity, rig-étaleness and rig-surjectivity, and
the universal étale-affine test by surjections of adic Noetherian rings with
kernel annihilated by an ideal of definition are equivalent. -/
theorem tfae_rigSmooth_rigSurjective {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [ClosedImmersion f] :
    List.TFAE
      [RigSmooth f ∧ RigSurjective f, RigEtale f ∧ RigSurjective f,
        etaleAffine_kernelKilled f] :=
  sorry

/-- For a closed immersion of locally Noetherian formal algebraic spaces,
being rig-smooth and rig-surjective is equivalent to being rig-étale and
rig-surjective. -/
theorem rigSmooth_and_rigSurjective_iff_rigEtale {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [ClosedImmersion f] :
    RigSmooth f ∧ RigSurjective f ↔ RigEtale f ∧ RigSurjective f :=
  (tfae_rigSmooth_rigSurjective f).out 0 1

/-- For a closed immersion of locally Noetherian formal algebraic spaces,
being rig-étale and rig-surjective is equivalent to the étale-affine kernel
test with `I * J = ⊥`. -/
theorem rigEtale_and_rigSurjective_iff_kernel {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [ClosedImmersion f] :
    RigEtale f ∧ RigSurjective f ↔ etaleAffine_kernelKilled f :=
  (tfae_rigSmooth_rigSurjective f).out 1 2

end AlgebraicGeometry.FormalAlgebraicSpace.ClosedImmersion
