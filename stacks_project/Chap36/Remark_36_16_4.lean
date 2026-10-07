module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Beilinson.Generation.Immersion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Generation.QuasiAffine

@[expose] public section

open CategoryTheory

universe u

section

variable {X Y : AlgebraicGeometry.Scheme.{u}}
variable [CompactSpace X] [QuasiSeparatedSpace X]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable (f : X ⟶ Y)

/- Remark 36.16.4 (1): for a morphism of quasi-compact and quasi-separated schemes,
derived pushforward reflects zero objects exactly when it reflects isomorphisms. -/
@[stacks 0BQT] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn.reflectsZero_iff_reflectsIsomorphisms f :
    (∀ K : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent X,
      CategoryTheory.Limits.IsZero
        ((AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn f).obj K) ↔
          CategoryTheory.Limits.IsZero K) ↔
      (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn f).ReflectsIsomorphisms)

/- Remark 36.16.4 (2): for a weak generator on the target, derived pushforward reflects zero
objects exactly when its derived pullback is a weak generator. -/
@[stacks 0BQT] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn.reflectsZero_iff_pullback_isWeakGenerator f :
    ∀ (E : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent Y),
      CategoryTheory.IsWeakGenerator E →
        ((∀ K : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent X,
          CategoryTheory.Limits.IsZero
            ((AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn f).obj K) ↔
              CategoryTheory.Limits.IsZero K) ↔
          CategoryTheory.IsWeakGenerator
            ((AlgebraicGeometry.Scheme.DerivedQCoh.pullback f).obj E)))

end

section

variable {X Y : AlgebraicGeometry.Scheme.{u}}
variable [CompactSpace X] [QuasiSeparatedSpace X]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable (f : X ⟶ Y) [AlgebraicGeometry.IsAffineHom f]

/- Remark 36.16.4 (3): derived pushforward along an affine morphism reflects isomorphisms. -/
@[stacks 0BQT] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn.reflectsIsomorphisms_of_isAffineHom f :
    (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn f).ReflectsIsomorphisms)

end

section

variable {X Y : AlgebraicGeometry.Scheme.{u}}
variable [CompactSpace X] [QuasiSeparatedSpace X]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f]

/- Remark 36.16.4 (4): derived pushforward along a quasi-compact open immersion reflects
isomorphisms. -/
@[stacks 0BQT] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn.reflectsIsomorphisms_of_isOpenImmersion f :
    (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn f).ReflectsIsomorphisms)

end

section

variable {X Y Z : AlgebraicGeometry.Scheme.{u}}
variable [CompactSpace X] [QuasiSeparatedSpace X]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [CompactSpace Z] [QuasiSeparatedSpace Z]
variable (f : X ⟶ Y) (g : Y ⟶ Z)
variable [(AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn f).ReflectsIsomorphisms]
variable [(AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn g).ReflectsIsomorphisms]

/- Remark 36.16.4 (5): conservativity of derived pushforward is stable under composition. -/
@[stacks 0BQT] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn.reflectsIsomorphisms_comp f g :
    (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn
      (f ≫ g)).ReflectsIsomorphisms)

end

/- Remark 36.16.4 (6): the degree-zero structure sheaf weakly generates the derived category
with quasicoherent cohomology on a quasi-affine scheme. -/
@[stacks 0BQT] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.structureSheaf_isWeakGenerator :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [X.IsQuasiAffine],
      CategoryTheory.IsWeakGenerator
        (AlgebraicGeometry.Scheme.DerivedQCoh.structureSheaf X))

section

variable (A : Type u) [CommRing A] (n : ℕ) {X : AlgebraicGeometry.Scheme.{u}}
variable (i : X ⟶ AlgebraicGeometry.ProjectiveSpace.scheme A n)
variable [AlgebraicGeometry.QuasiCompact i] [AlgebraicGeometry.IsImmersion i]

/- Remark 36.16.4 (7): the pullback of the derived Beilinson generator to a quasi-compact
locally closed subscheme of projective space is a weak generator. -/
@[stacks 0BQT] #check
  (AlgebraicGeometry.ProjectiveSpace.pullbackDerivedBeilinsonGenerator_isWeakGenerator
    A n i :
      CategoryTheory.IsWeakGenerator
        ((AlgebraicGeometry.Scheme.DerivedQCoh.pullback i).obj
          (AlgebraicGeometry.ProjectiveSpace.derivedBeilinsonGenerator A n)))

end
