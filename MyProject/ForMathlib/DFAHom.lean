import Mathlib.Computability.DFA

/-!
# Morphisms between DFAs

This file defines morphisms between DFAs, which are bundled functions between the state spaces
that respect the transition function, start state, and accept states of the DFAs.

## Main definitions

* `DFA.Hom` - A morphism from the `DFA` `M` to the `DFA` `N`

* `DFA.Equiv` - An equivalence of `DFA`s, which is a bijective morphism

* `DFA.HomSurj` - A surjective DFA morphism.

## Main theorems

* `DFA.Hom.pres_lang` - `M.accepts = N.accepts` when there exists `f : M → N`.

## Notation

* `M → N` - Notation for `DFA.Hom M N`.

* `M ≃ N` - Notation for `DFA.Equiv M N`.

* `M ↠ N` - Notation for `DFA.HomSurj M N`.

## TODO

Prove that equivalence is symmetric and transitive
-/

namespace DFA

universe u v w

variable {α : Type u} {σ₁ : Type v} {σ₂ : Type w}

/-- A morphism of DFAs from `M` to `N`. -/
structure Hom (M : DFA α σ₁) (N : DFA α σ₂) where
  /-- Underlying function map from states of `M` to states of `N`. -/
  toFun : σ₁ → σ₂
  /-- The function preserves the start state. -/
  map_start : toFun M.start = N.start
  /-- The function preserves the set of accepting states. -/
  map_accept (q : σ₁) : q ∈ M.accept ↔ toFun q ∈ N.accept
  /-- The function preserves state transitions. -/
  map_step (q : σ₁) (w : List α) : toFun (M.evalFrom q w) = N.evalFrom (toFun q) w

/-- `M → N` denotes the type of `DFA.Hom M N`. -/
infixr:25 " → " => Hom

variable {M : DFA α σ₁} {N : DFA α σ₂}

section coe

instance Hom.funLike : FunLike (M → N) σ₁ σ₂ where
  coe := Hom.toFun
  coe_injective' f g h := by cases f; cases g; congr

@[simp]
theorem Hom.coe_mk (f : σ₁ → σ₂) (h₁ h₂ h₃) :
  (Hom.mk (M := M) (N := N) f h₁ h₂ h₃ : M → N) = f := rfl

/-- Two DFA morphisms are equal if they are defined by the same underlying function. -/
theorem Hom.ext {f g : M → N} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

end coe

/-- Given a DFA morphism `f : M → N`, the language accepted by `M` from state `s` is equal to
the language accepted by `N` from `f s`. -/
lemma Hom.pres_acceptsFrom {M : DFA α σ₁} {N : DFA α σ₂} (f : M → N) (s : σ₁) :
    M.acceptsFrom s = N.acceptsFrom (f.toFun s) := by
  ext w
  simp_all [mem_acceptsFrom]
  rw [← f.map_step, f.map_accept]

/-- A morphism of DFAs preserves the accepted language. -/
theorem Hom.pres_lang (f : M → N) : M.accepts = N.accepts := by
  ext w
  simp_all [mem_accepts, eval]
  constructor
  · intro h
    rwa [f.map_accept, f.map_step M.start w, f.map_start] at h
  · intro h
    rwa [f.map_accept, f.map_step M.start w, f.map_start]

/-- The identity morphism on a DFA. -/
def homRefl (M : DFA α σ₁) : M → M where
  toFun := id
  map_start := by rfl
  map_accept := by intro q; simp
  map_step := by intro q w; simp

/-- An equivalence of DFAs is a bijective morphism. -/
structure Equiv (M : DFA α σ₁) (N : DFA α σ₂) where
  /-- The bijection between the state spaces -/
  statesEquiv : σ₁ ≃ σ₂
  /-- The equivalence preserves the start state. -/
  map_start : statesEquiv M.start = N.start
  /-- The equivalence preserves the set of accepting states. -/
  map_accept (q : σ₁) : q ∈ M.accept ↔ statesEquiv q ∈ N.accept
  /-- The equivalence preserves state transitions. -/
  map_step (q : σ₁) (w : List α) : statesEquiv (M.evalFrom q w) = N.evalFrom (statesEquiv q) w

/-- `M ≃ N` denotes the type of `DFA.Equiv M N`. -/
infixr:25 " ≃ " => Equiv

def Equiv.toHom (e : M ≃ N) : M → N where
  toFun := e.statesEquiv
  map_start := e.map_start
  map_accept := e.map_accept
  map_step := e.map_step

section coe

instance : EquivLike (M ≃ N) σ₁ σ₂ where
  coe f := f.statesEquiv
  inv f := f.statesEquiv.invFun
  left_inv f := f.statesEquiv.left_inv
  right_inv f := f.statesEquiv.right_inv
  coe_injective' f g h₁ h₂ := by
    cases f
    cases g
    congr
    apply Equiv.coe_fn_injective h₁

-- shortcut instance that doesn't generate any subgoals
instance : CoeFun (M ≃ N) fun _ ↦ σ₁ → σ₂ where
  coe f := f.statesEquiv

/-- Two equivalences agree if they are defined by the same underlying function. -/
theorem Equiv.ext {f g : M ≃ N} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

protected theorem Equiv.congr_arg {f : M ≃ N} {x x' : σ₁} : x = x' → f x = f x' :=
  DFunLike.congr_arg f

protected theorem Equiv.congr_fun {f g : M ≃ N} (h : f = g) (x : σ₁) : f x = g x :=
  DFunLike.congr_fun h x

@[simp]
theorem Equiv.coe_mk (f : σ₁ ≃ σ₂) (h₁ h₂ h₃) :
  (Equiv.mk (M := M) (N := N) f h₁ h₂ h₃ : M ≃ N) = f := rfl

@[simp]
theorem Equiv.mk_coe (e : M ≃ N) (e' h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨e, e', h₁, h₂⟩, h₃, h₄, h₅⟩ : M ≃ N) = e :=
  ext fun _ => rfl

theorem Equiv.statesEquiv_eq_coe (f : M ≃ N) : f.statesEquiv = f :=
  rfl

/-- `simp`-normal form of `statesEquiv_eq_coe`. -/
@[simp]
theorem Equiv.coe_toEquiv (f : M ≃ N) : ⇑(f : M ≃ N) = f := rfl

end coe

/-- The identity equivalence on a DFA. -/
def equivRefl (M : DFA α σ₁) : M ≃ M where
  statesEquiv := Equiv.refl σ₁
  map_start := by rfl
  map_accept := by simp
  map_step := by simp

def Equiv.symm (e : M ≃ N) : N ≃ M where
  statesEquiv := e.statesEquiv.symm
  map_start := by
    rw [← Equiv.symm_apply_apply e.statesEquiv M.start, e.map_start]
  map_accept := by
    intro q
    simp [e.map_accept]
  map_step := by
    intro q w
    rw [← Equiv.symm_apply_apply e.statesEquiv (M.evalFrom (e.statesEquiv.symm q) w)]
    simp [e.map_step]

variable {σ₃ : Type*} {O : DFA α σ₃} in
def Equiv.trans (e₁ : M ≃ N) (e₂ : N ≃ O) : M ≃ O where
  statesEquiv := _root_.Equiv.trans e₁.statesEquiv e₂.statesEquiv
  map_start := by simp [e₁.map_start, e₂.map_start]
  map_accept := by simp [e₁.map_accept, e₂.map_accept]
  map_step := by simp [e₁.map_step, e₂.map_step]

/-! ### Surjective Morphisms -/

/-- A structure extending `DFA.Hom` asserting that the morphism is surjective -/
structure HomSurj (M : DFA α σ₁) (N : DFA α σ₂) extends f : M → N where
  /-- The function is surjective. -/
  surjective : Function.Surjective f

/-- `M ↠ N` denotes the type of `DFA.HomSurj M N`. -/
infixr:25 " ↠ " => HomSurj

/-- Forget the surjectivity proof and view `HomSurj` as a DFA morphism. -/
def HomSurj.toDFAHom (f : M ↠ N) : M → N where
  toFun := f.toFun
  map_start := f.map_start
  map_accept := f.map_accept
  map_step := f.map_step

section coe

instance HomSurj.funLike : FunLike (M → N) σ₁ σ₂ where
  coe := Hom.toFun
  coe_injective' f g h := by cases f; cases g; congr

@[simp]
theorem HomSurj.coe_mk (f : σ₁ → σ₂) (h₁ h₂ h₃) :
  (Hom.mk (M := M) (N := N) f h₁ h₂ h₃ : M → N) = f := rfl

/-- Two DFA morphisms are equal if they are defined by the same underlying function. -/
theorem HomSurj.ext {f g : M → N} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

end coe

/-- Lift a `HomSurj` that is also injective into an `Equiv` by using the
noncomputable inverse function `f.toFun.surjInv f.surjective` -/
noncomputable def HomSurj.equivOfInj (f : M ↠ N) (hf : f.toFun.Injective) : M ≃ N where
  statesEquiv := by
    refine _root_.Equiv.mk (f.toFun) (f.toFun.surjInv f.surjective) ?_ ?_
    · have hbij : f.toFun.Bijective := by
        simp_all [Function.Bijective]
        apply f.surjective
      exact Function.leftInverse_surjInv hbij
    · exact Function.rightInverse_surjInv f.surjective
  map_start := f.map_start
  map_accept := f.map_accept
  map_step := f.map_step

end DFA
