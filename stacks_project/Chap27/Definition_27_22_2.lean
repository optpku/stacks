module

public import ReasLib.AlgebraicGeometry.Grassmannian.BaseChange
public import stacks_project.Chap27.Lemma_27_22_1
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 27.22.2: for `0 < k < n`, an explicit representing model supplies the
Grassmannian scheme over `ℤ`. -/
@[stacks 089U] #check (AlgebraicGeometry.Grassmannian.Model.scheme :
  ∀ {k n : ℕ} {hk : 0 < k} {hkn : k < n},
    AlgebraicGeometry.Grassmannian.Model.{u} k n hk hkn → AlgebraicGeometry.Scheme.{u})

/- The Grassmannian functor assigns quotient classes to schemes. -/
#check (AlgebraicGeometry.Grassmannian.functor :
  ∀ (k n : ℕ), CategoryTheory.Functor
    (Opposite (AlgebraicGeometry.Scheme.{u})) (Type (u + 1)))

/- The Grassmannian functor is representable when `0 < k < n`. -/
#check (AlgebraicGeometry.Grassmannian.functor_isRepresentable :
  ∀ (k n : ℕ), 0 < k → k < n →
    CategoryTheory.Functor.IsRepresentable (AlgebraicGeometry.Grassmannian.functor k n))

/- A Grassmannian model records the representing scheme, its universal point, and the
representability law. -/
#check (AlgebraicGeometry.Grassmannian.Model :
  ∀ (k n : ℕ), 0 < k → k < n → Type (u + 1))

/- An explicit scheme, universal point, and representability law determine a model. -/
#check (AlgebraicGeometry.Grassmannian.Model.ofPoint :
  ∀ {k n : ℕ} (hk : 0 < k) (hkn : k < n) (X : AlgebraicGeometry.Scheme.{u})
    (x : (AlgebraicGeometry.Grassmannian.functor k n).obj (Opposite.op X)),
      (AlgebraicGeometry.Grassmannian.functor k n).IsRepresentedBy x →
        AlgebraicGeometry.Grassmannian.Model.{u} k n hk hkn)

/- An explicit Grassmannian model carries its universal point. -/
#check (AlgebraicGeometry.Grassmannian.Model.point :
  ∀ {k n : ℕ} {hk : 0 < k} {hkn : k < n}
    (P : AlgebraicGeometry.Grassmannian.Model.{u} k n hk hkn),
      (AlgebraicGeometry.Grassmannian.functor k n).obj
        (Opposite.op P.scheme))

/- The universal point of a Grassmannian model represents the Grassmannian functor. -/
#check (AlgebraicGeometry.Grassmannian.Model.isRepresentedBy :
  ∀ {k n : ℕ} {hk : 0 < k} {hkn : k < n}
    (P : AlgebraicGeometry.Grassmannian.Model.{u} k n hk hkn),
      (AlgebraicGeometry.Grassmannian.functor k n).IsRepresentedBy P.point)

/- Representability of the Grassmannian functor gives existence of an explicit model. -/
#check (AlgebraicGeometry.Grassmannian.model_nonempty :
  ∀ (k n : ℕ) (hk : 0 < k) (hkn : k < n),
    Nonempty (AlgebraicGeometry.Grassmannian.Model.{u} k n hk hkn))

/- The Grassmannian over a scheme is the base change of an explicit integral model. -/
#check (AlgebraicGeometry.Grassmannian.baseChange :
  ∀ {k n : ℕ} {hk : 0 < k} {hkn : k < n},
    AlgebraicGeometry.Grassmannian.Model.{u} k n hk hkn →
      AlgebraicGeometry.Scheme.{u} → AlgebraicGeometry.Scheme.{u})

/- A base-changed Grassmannian has its canonical projection to the base scheme. -/
#check (AlgebraicGeometry.Grassmannian.toBase :
  ∀ {k n : ℕ} {hk : 0 < k} {hkn : k < n}
    (P : AlgebraicGeometry.Grassmannian.Model.{u} k n hk hkn)
    (S : AlgebraicGeometry.Scheme.{u}),
      AlgebraicGeometry.Grassmannian.baseChange P S ⟶ S)

/- The Grassmannian over a commutative ring is its base change to the spectrum of that ring. -/
#check (AlgebraicGeometry.Grassmannian.overRing :
  ∀ {k n : ℕ} {hk : 0 < k} {hkn : k < n},
    AlgebraicGeometry.Grassmannian.Model.{u} k n hk hkn →
      ∀ (R : Type u), [CommRing R] → AlgebraicGeometry.Scheme.{u})
