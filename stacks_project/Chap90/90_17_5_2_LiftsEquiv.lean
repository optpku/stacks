module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SelfPullback
public import ReasLib.CategoryTheory.Fibered.Lifts.Pushforward

/-!
# Compatibility view of lift transport and the self-pullback comparison
-/

@[expose] public section

open CategoryTheory

universe v₁ u₁ v₂ u₂ u v w

section LiftTransport

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]
variable {p : 𝒳 ⥤ 𝒮} {R S T : 𝒮}
variable {f g : R ⟶ S} (h : f = g) {x : p.Fiber S}
variable (a : Functor.ObjectLift p f x)

/- 90.17.5.2 lift transport compatibility -/
#check (CategoryTheory.Functor.ObjectLift.congr_hom h a :
  (Functor.ObjectLift.congr h a).hom = a.hom)

variable [Functor.IsFibered.InGroupoids p.op]
variable (projection : R ⟶ S) (baseMap : S ⟶ T) {baseObject : p.Fiber T}
variable (lift : Functor.ObjectLift p (projection ≫ baseMap) baseObject)

#check (CategoryTheory.Functor.ObjectLift.pushforwardAlong_spec projection baseMap lift :
  p.IsHomLift baseMap (Functor.ObjectLift.pushforwardAlong projection baseMap lift).hom ∧
    p.obj (Functor.ObjectLift.pushforwardAlong projection baseMap lift).left = S)

end LiftTransport

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k} [Functor.HasRimSchlessinger p]
variable {A A' : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
variable (hf : Function.Surjective f.hom) (x : p.Fiber A)

#check (CategoryTheory.Functor.liftsSelfPullbackEquiv f hf x :
  Functor.lifts p f x × Functor.lifts p f x ≃
    Functor.lifts p (ArtinianLocalAlgCat.selfPullbackToBase f) x)
