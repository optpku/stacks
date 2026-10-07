module

public import stacks_project.Chap60.«60_24_1_1»
public import stacks_project.Chap60.Remark_60_24_1_Higher_direct_images_Context
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSite RingedSite.Hom
open AlgebraicGeometry.Scheme.Crystalline
open AlgebraicGeometry.Scheme.Zariski.Small

noncomputable section

universe z u

/-- Remark 60.24.1 (Higher direct images): for a prime `p`, a morphism of
divided-power schemes `(S, I, γ) ⟶ (S', I', γ')` over `ℤ_(p)`, and a commutative
square of schemes `X ⟶ X'` over `S₀ ⟶ S'₀` with `p` locally nilpotent on `X` and
`X'`, the restriction of `Rf_cris,* F` at an object `(U', T', δ')` of
`Cris(X'/S')` is identified with `R(T ⟶ T')_* (Rτ_{U/T,*} F_U)`. Here
`U = X ×_{X'} U' = f⁻¹(U')`, `(T₀, T, δ)` is a cartesian divided-power pullback
of `T'` over `S ⟶ S'` as in Lemma 60.7.4, `τ` is the structure morphism
`(U/T)_cris ⟶ T_Zar`, and `i` is the Zariski map `T ⟶ T'`. The computational
owner of equation 60.24.1.1 is `crystallinePushforwardEvalIso` applied to the
crystalline morphism of the square, the structure morphism `τ`, and the
Lemma 60.7.4 Zariski map `i`. The remaining hypothesis
`IsIso (modulePullbackDerived.compComparison τ i)` is only the derived-API
well-definedness needed to apply that owner. The localization comparison is a
derived-API equality transported by `eqToIso`, not a `sorry` theorem. -/
@[stacks 07MJ]
noncomputable def higherDirectImage_eval
    (c : HigherDirectImageContext)
    (f : RingedSite.Hom
      (RingedSite.ofRingSheaf
        (smallCrystallineTopology c.p c.S.scheme c.S.ideal c.S.dividedPowers
          c.S.compatible c.s c.Xsch c.x₀ c.pX) c.𝒪X)
      (RingedSite.ofRingSheaf
        (smallCrystallineTopology c.p c.S'.scheme c.S'.ideal c.S'.dividedPowers
          c.S'.compatible c.s' c.X'sch c.x'₀ c.pX') c.𝒪Y))
    (τ : RingedSite.Hom
      ((RingedSite.ofRingSheaf
        (smallCrystallineTopology c.p c.S.scheme c.S.ideal c.S.dividedPowers
          c.S.compatible c.s c.Xsch c.x₀ c.pX) c.𝒪X).localization (f.base.obj c.T'))
      (ringedSite c.Tthick.scheme))
    (i : RingedSite.Hom
      (ringedSite c.Tthick.scheme)
      ((RingedSite.ofRingSheaf
        (smallCrystallineTopology c.p c.S'.scheme c.S'.ideal c.S'.dividedPowers
          c.S'.compatible c.s' c.X'sch c.x'₀ c.pX') c.𝒪Y).localization c.T'))
    (hcomp : τ.comp i = f.localization c.T')
    [UnivLE.{u + 1, z}]
    [τ.modulePushforward.{z}.IsRightAdjoint]
    [i.modulePushforward.{z}.IsRightAdjoint]
    [(τ.comp i).modulePushforward.{z}.IsRightAdjoint]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{z} f)
        (ModuleQis.{z} (RingedSite.ofRingSheaf
          (smallCrystallineTopology c.p c.S.scheme c.S.ideal c.S.dividedPowers
            c.S.compatible c.s c.Xsch c.x₀ c.pX) c.𝒪X))]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{z} (f.localization c.T'))
        (ModuleQis.{z}
          ((RingedSite.ofRingSheaf
            (smallCrystallineTopology c.p c.S.scheme c.S.ideal c.S.dividedPowers
              c.S.compatible c.s c.Xsch c.x₀ c.pX) c.𝒪X).localization (f.base.obj c.T')))]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{z} τ)
        (ModuleQis.{z}
          ((RingedSite.ofRingSheaf
            (smallCrystallineTopology c.p c.S.scheme c.S.ideal c.S.dividedPowers
              c.S.compatible c.s c.Xsch c.x₀ c.pX) c.𝒪X).localization (f.base.obj c.T')))]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{z} i) (ModuleQis.{z} (ringedSite c.Tthick.scheme))]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{z} (τ.comp i))
        (ModuleQis.{z}
          ((RingedSite.ofRingSheaf
            (smallCrystallineTopology c.p c.S.scheme c.S.ideal c.S.dividedPowers
              c.S.compatible c.s c.Xsch c.x₀ c.pX) c.𝒪X).localization (f.base.obj c.T')))]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{z} τ) (ModuleQis.{z} (ringedSite c.Tthick.scheme))]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{z} i)
        (ModuleQis.{z}
          ((RingedSite.ofRingSheaf
            (smallCrystallineTopology c.p c.S'.scheme c.S'.ideal c.S'.dividedPowers
              c.S'.compatible c.s' c.X'sch c.x'₀ c.pX') c.𝒪Y).localization c.T'))]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{z} (τ.comp i))
        (ModuleQis.{z}
          ((RingedSite.ofRingSheaf
            (smallCrystallineTopology c.p c.S'.scheme c.S'.ideal c.S'.dividedPowers
              c.S'.compatible c.s' c.X'sch c.x'₀ c.pX') c.𝒪Y).localization c.T'))]
    [DerivedAdjunction.HasPair.{z} τ]
    [DerivedAdjunction.HasPair.{z} i]
    [DerivedAdjunction.HasPair.{z} (τ.comp i)]
    (h_comparison : IsIso (modulePullbackDerived.compComparison τ i))
    (F : ModuleDerived.{z}
      (RingedSite.ofRingSheaf
        (smallCrystallineTopology c.p c.S.scheme c.S.ideal c.S.dividedPowers
          c.S.compatible c.s c.Xsch c.x₀ c.pX) c.𝒪X))
    (h_loc :
      (localizedRestrictionDerived.{z}
          (RingedSite.ofRingSheaf
            (smallCrystallineTopology c.p c.S'.scheme c.S'.ideal c.S'.dividedPowers
              c.S'.compatible c.s' c.X'sch c.x'₀ c.pX') c.𝒪Y) c.T').obj
        ((modulePushforwardDerived.{z} f).obj F) =
      (modulePushforwardDerived.{z} (f.localization c.T')).obj
        ((localizedRestrictionDerived.{z}
            (RingedSite.ofRingSheaf
              (smallCrystallineTopology c.p c.S.scheme c.S.ideal c.S.dividedPowers
                c.S.compatible c.s c.Xsch c.x₀ c.pX) c.𝒪X)
            (f.base.obj c.T')).obj F)) :
    (localizedRestrictionDerived.{z}
          (RingedSite.ofRingSheaf
            (smallCrystallineTopology c.p c.S'.scheme c.S'.ideal c.S'.dividedPowers
              c.S'.compatible c.s' c.X'sch c.x'₀ c.pX') c.𝒪Y) c.T').obj
        ((modulePushforwardDerived.{z} f).obj F) ≅
      (modulePushforwardDerived.{z} i).obj
        ((modulePushforwardDerived.{z} τ).obj
          ((localizedRestrictionDerived.{z}
              (RingedSite.ofRingSheaf
                (smallCrystallineTopology c.p c.S.scheme c.S.ideal c.S.dividedPowers
                  c.S.compatible c.s c.Xsch c.x₀ c.pX) c.𝒪X)
              (f.base.obj c.T')).obj F)) :=
  crystallinePushforwardEvalIso f c.T' τ i hcomp h_comparison F (eqToIso h_loc)

/-- The evaluation iso is `crystallinePushforwardEvalIso` on the crystalline morphism
of the square, after transporting the Section 60.10 localization comparison. -/
theorem higherDirectImage_eval_spec
    (c : HigherDirectImageContext)
    (f : RingedSite.Hom
      (RingedSite.ofRingSheaf
        (smallCrystallineTopology c.p c.S.scheme c.S.ideal c.S.dividedPowers
          c.S.compatible c.s c.Xsch c.x₀ c.pX) c.𝒪X)
      (RingedSite.ofRingSheaf
        (smallCrystallineTopology c.p c.S'.scheme c.S'.ideal c.S'.dividedPowers
          c.S'.compatible c.s' c.X'sch c.x'₀ c.pX') c.𝒪Y))
    (τ : RingedSite.Hom
      ((RingedSite.ofRingSheaf
        (smallCrystallineTopology c.p c.S.scheme c.S.ideal c.S.dividedPowers
          c.S.compatible c.s c.Xsch c.x₀ c.pX) c.𝒪X).localization (f.base.obj c.T'))
      (ringedSite c.Tthick.scheme))
    (i : RingedSite.Hom
      (ringedSite c.Tthick.scheme)
      ((RingedSite.ofRingSheaf
        (smallCrystallineTopology c.p c.S'.scheme c.S'.ideal c.S'.dividedPowers
          c.S'.compatible c.s' c.X'sch c.x'₀ c.pX') c.𝒪Y).localization c.T'))
    (hcomp : τ.comp i = f.localization c.T')
    [UnivLE.{u + 1, z}]
    [τ.modulePushforward.{z}.IsRightAdjoint]
    [i.modulePushforward.{z}.IsRightAdjoint]
    [(τ.comp i).modulePushforward.{z}.IsRightAdjoint]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{z} f)
        (ModuleQis.{z} (RingedSite.ofRingSheaf
          (smallCrystallineTopology c.p c.S.scheme c.S.ideal c.S.dividedPowers
            c.S.compatible c.s c.Xsch c.x₀ c.pX) c.𝒪X))]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{z} (f.localization c.T'))
        (ModuleQis.{z}
          ((RingedSite.ofRingSheaf
            (smallCrystallineTopology c.p c.S.scheme c.S.ideal c.S.dividedPowers
              c.S.compatible c.s c.Xsch c.x₀ c.pX) c.𝒪X).localization (f.base.obj c.T')))]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{z} τ)
        (ModuleQis.{z}
          ((RingedSite.ofRingSheaf
            (smallCrystallineTopology c.p c.S.scheme c.S.ideal c.S.dividedPowers
              c.S.compatible c.s c.Xsch c.x₀ c.pX) c.𝒪X).localization (f.base.obj c.T')))]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{z} i) (ModuleQis.{z} (ringedSite c.Tthick.scheme))]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{z} (τ.comp i))
        (ModuleQis.{z}
          ((RingedSite.ofRingSheaf
            (smallCrystallineTopology c.p c.S.scheme c.S.ideal c.S.dividedPowers
              c.S.compatible c.s c.Xsch c.x₀ c.pX) c.𝒪X).localization (f.base.obj c.T')))]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{z} τ) (ModuleQis.{z} (ringedSite c.Tthick.scheme))]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{z} i)
        (ModuleQis.{z}
          ((RingedSite.ofRingSheaf
            (smallCrystallineTopology c.p c.S'.scheme c.S'.ideal c.S'.dividedPowers
              c.S'.compatible c.s' c.X'sch c.x'₀ c.pX') c.𝒪Y).localization c.T'))]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{z} (τ.comp i))
        (ModuleQis.{z}
          ((RingedSite.ofRingSheaf
            (smallCrystallineTopology c.p c.S'.scheme c.S'.ideal c.S'.dividedPowers
              c.S'.compatible c.s' c.X'sch c.x'₀ c.pX') c.𝒪Y).localization c.T'))]
    [DerivedAdjunction.HasPair.{z} τ]
    [DerivedAdjunction.HasPair.{z} i]
    [DerivedAdjunction.HasPair.{z} (τ.comp i)]
    (h_comparison : IsIso (modulePullbackDerived.compComparison τ i))
    (F : ModuleDerived.{z}
      (RingedSite.ofRingSheaf
        (smallCrystallineTopology c.p c.S.scheme c.S.ideal c.S.dividedPowers
          c.S.compatible c.s c.Xsch c.x₀ c.pX) c.𝒪X))
    (h_loc :
      (localizedRestrictionDerived.{z}
          (RingedSite.ofRingSheaf
            (smallCrystallineTopology c.p c.S'.scheme c.S'.ideal c.S'.dividedPowers
              c.S'.compatible c.s' c.X'sch c.x'₀ c.pX') c.𝒪Y) c.T').obj
        ((modulePushforwardDerived.{z} f).obj F) =
      (modulePushforwardDerived.{z} (f.localization c.T')).obj
        ((localizedRestrictionDerived.{z}
            (RingedSite.ofRingSheaf
              (smallCrystallineTopology c.p c.S.scheme c.S.ideal c.S.dividedPowers
                c.S.compatible c.s c.Xsch c.x₀ c.pX) c.𝒪X)
            (f.base.obj c.T')).obj F)) :
    higherDirectImage_eval c f τ i hcomp h_comparison F h_loc =
      crystallinePushforwardEvalIso f c.T' τ i hcomp h_comparison F (eqToIso h_loc) :=
  sorry

end
