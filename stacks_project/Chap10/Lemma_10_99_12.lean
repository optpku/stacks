module

public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Projective
public import ReasLib.Algebra.Homology.ShortComplex.ChangeOfRings

/-!
# First Tor under successive scalar extension

@stack 00MM
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace ModuleCat.ExtendScalars.TorOne

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- The coefficient-first degree-one derived scalar-extension owner for `Tor₁`. -/
noncomputable abbrev obj (f : R →+* S) (M : ModuleCat R) : ModuleCat S :=
  ((ModuleCat.extendScalars f).leftDerived 1).obj M

/-- The source of the degree-one comparison after a second scalar extension. -/
noncomputable abbrev baseChangeSource
    (f : R →+* S) (g : S →+* T) (M : ModuleCat R) : ModuleCat T :=
  (ModuleCat.extendScalars g).obj (obj f M)

/-- The target degree-one owner for the composite scalar extension. -/
noncomputable abbrev baseChangeTarget
    (f : R →+* S) (g : S →+* T) (M : ModuleCat R) : ModuleCat T :=
  obj (g.comp f) M

/-- In the downward complex shape, the predecessor of degree `1` is degree `2`. -/
theorem down_prev_one : (ComplexShape.down ℕ).prev 1 = 2 := sorry

/-- In the downward complex shape, the successor of degree `1` is degree `0`. -/
theorem down_next_one : (ComplexShape.down ℕ).next 1 = 0 := sorry

/-- The `2 → 1 → 0` scalar-extended projective-resolution window computing `Tor₁`. -/
noncomputable def window (f : R →+* S) (M : ModuleCat R) :
    ShortComplex (ModuleCat S) :=
  (HomologicalComplex.shortComplexFunctor' (ModuleCat S) (ComplexShape.down ℕ) 2 1 0).obj
    (((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (CategoryTheory.projectiveResolution M).complex)

/-- The degree-one derived scalar-extension owner is the homology of its projective-resolution
window. -/
noncomputable def windowIso (f : R →+* S) (M : ModuleCat R) :
    obj f M ≅ ShortComplex.homology (window f M) :=
  (CategoryTheory.projectiveResolution M).isoLeftDerivedObj
      (ModuleCat.extendScalars f) 1 ≪≫
    (HomologicalComplex.homologyFunctorIso' (ModuleCat S) (ComplexShape.down ℕ)
      2 1 0 down_prev_one down_next_one).app
        (((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (CategoryTheory.projectiveResolution M).complex)

/-- Applying the second scalar extension to the first window identifies it with the window for
the composite ring map. -/
noncomputable def baseChangeWindowIso
    (f : R →+* S) (g : S →+* T) (M : ModuleCat R) :
    ((ModuleCat.extendScalars g).mapShortComplex.obj (window f M)) ≅
      window (g.comp f) M :=
  (HomologicalComplex.shortComplexFunctor' (ModuleCat T) (ComplexShape.down ℕ) 2 1 0).mapIso
    ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp f g).symm
      (ComplexShape.down ℕ)).app (CategoryTheory.projectiveResolution M).complex)

/-- The natural degree-one comparison
`Tor₁^R(M, S) ⊗[S] T ⟶ Tor₁^R(M, T)`, on coefficient-first derived owners. -/
noncomputable def baseChange
    (f : R →+* S) (g : S →+* T) (M : ModuleCat R) :
    baseChangeSource f g M ⟶ baseChangeTarget f g M :=
  ((ModuleCat.extendScalars g).mapIso (windowIso f M)).hom ≫
    ModuleCat.ExtendScalars.HomologyComparison.map g (window f M) ≫
      (ShortComplex.homologyMapIso (baseChangeWindowIso f g M)).hom ≫
        (windowIso (g.comp f) M).inv

/-- Lemma 10.99.12: if the scalar extension of `M` from `R` to `S` is flat over `S`, then the
natural map `Tor₁^R(M, S) ⊗[S] T → Tor₁^R(M, T)` is surjective. -/
@[stacks 00MM]
theorem baseChange_surjective_of_flat
    (f : R →+* S) (g : S →+* T) (M : ModuleCat R)
    (hflat : Module.Flat S ((ModuleCat.extendScalars f).obj M)) :
    Function.Surjective (baseChange f g M).hom := sorry

end ModuleCat.ExtendScalars.TorOne

#check @ModuleCat.ExtendScalars.TorOne.obj
#check @ModuleCat.ExtendScalars.TorOne.baseChange
#check @ModuleCat.ExtendScalars.TorOne.baseChange_surjective_of_flat

#print axioms ModuleCat.ExtendScalars.TorOne.baseChange
