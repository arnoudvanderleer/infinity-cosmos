/-
Copyright (c) 2024 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johns Hopkins Category Theory Seminar
-/

import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.CompStruct
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialCategory.Basic

universe u v

open CategoryTheory

namespace CategoryTheory

/-- This is the free-living isomorphism as a category with objects called
`zero` and `one`. Perhaps these should have different names?-/
def WalkingIso : Type := Fin 2

def WalkingIso.zero : WalkingIso := (0 : Fin 2)
def WalkingIso.one : WalkingIso := (1 : Fin 2)

open WalkingIso

namespace WalkingIso

/-- The free isomorphism is the codiscrete category on two objects. Can we make this a special
case of the other definition?-/
instance : Category (WalkingIso) where
  Hom _ _ := Unit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩

section

variable {C : Type u} [Category.{v} C]

/-- Functors out of `WalkingIso` define isomorphisms in the target category.-/
def toIso  (F : WalkingIso ⥤ C) : (F.obj zero) ≅ (F.obj one) where
  hom := F.map PUnit.unit
  inv := F.map PUnit.unit
  hom_inv_id := by rw [← F.map_comp, ← F.map_id]; rfl
  inv_hom_id := by rw [← F.map_comp, ← F.map_id]; rfl

/-- From an isomorphism in a category, one can build a functor out of `WalkingIso` to
that category.-/
def fromIso {X Y : C} (e : X ≅ Y) : WalkingIso ⥤ C where
  obj := fun
    | (0 : Fin 2) => X
    | (1 : Fin 2) => Y
  map := @fun
    | (0 : Fin 2), (0 : Fin 2), _ => 𝟙 _
    | (0 : Fin 2), (1 : Fin 2),  _ => e.hom
    | (1 : Fin 2), (0 : Fin 2), _ => e.inv
    | (1 : Fin 2), (1 : Fin 2),  _ => 𝟙 _
  map_comp := by simp [WalkingIso, Quiver.Hom]

def equiv : (WalkingIso ⥤ C) ≃ Σ (X : C) (Y : C), (X ≅ Y) where
  toFun F := ⟨F.obj zero, F.obj one, toIso F⟩
  invFun p := fromIso p.2.2
  right_inv := fun ⟨X, Y, e⟩ ↦ rfl
  left_inv F := by
    apply Functor.hext
    · simp [WalkingIso]
      constructor <;> rfl
    · simp [WalkingIso]
      simp only [fromIso, toIso]
      constructor <;> constructor <;>
      ( intro ⟨⟩
        try rfl
        try (rw [← F.map_id]; rfl) )

end

def coev (i : WalkingIso) : Fin 1 ⥤ WalkingIso := ComposableArrows.mk₀ i

end WalkingIso

end CategoryTheory

namespace SSet

open Simplicial Edge

def coherentIso : SSet := nerve WalkingIso

namespace coherentIso

def equivFun {n : ℕ} : coherentIso _⦋n⦌ ≃ (Fin (n + 1) → Fin 2) where
  toFun f := f.obj
  invFun f := .mk f (fun _ ↦ ⟨⟩) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
  left_inv _ := rfl
  right_inv _ := rfl

instance (n : ℕ) : DecidableEq (coherentIso _⦋n⦌) :=
  fun _ _ ↦ decidable_of_iff _ (Equiv.apply_eq_iff_eq coherentIso.equivFun)


def x₀ : coherentIso _⦋0⦌ :=
  ComposableArrows.mk₀ WalkingIso.zero

def x₁ : coherentIso _⦋0⦌ :=
  ComposableArrows.mk₀ WalkingIso.one

def hom : Edge x₀ x₁ where
  edge := ComposableArrows.mk₁ ⟨⟩
  src_eq := ComposableArrows.ext₀ rfl
  tgt_eq := ComposableArrows.ext₀ rfl

def inv : Edge x₁ x₀ where
  edge := ComposableArrows.mk₁ ⟨⟩
  src_eq := ComposableArrows.ext₀ rfl
  tgt_eq := ComposableArrows.ext₀ rfl

def homInvId : Edge.CompStruct hom inv (Edge.id x₀) where
  simplex := ComposableArrows.mk₂ ⟨⟩ ⟨⟩
  d₂ := ComposableArrows.ext₁ rfl rfl rfl
  d₀ := ComposableArrows.ext₁ rfl rfl rfl
  d₁ := ComposableArrows.ext₁ rfl rfl rfl

def invHomId : Edge.CompStruct inv hom (Edge.id x₁) where
  simplex := ComposableArrows.mk₂ ⟨⟩ ⟨⟩
  d₂ := ComposableArrows.ext₁ rfl rfl rfl
  d₀ := ComposableArrows.ext₁ rfl rfl rfl
  d₁ := ComposableArrows.ext₁ rfl rfl rfl

def isIsoHom : Edge.IsIso coherentIso.hom where
  inv := inv
  homInvId := homInvId
  invHomId := invHomId

def isIsoMapHom
  {X : SSet}
  (g : coherentIso ⟶ X)
  : IsIso (coherentIso.hom.map g)
  := isIsoHom.map g

def isIsoOfEqMapHom
  {X : SSet}
  {x₀ x₁ : X _⦋0⦌}
  {f : Edge x₀ x₁}
  {g : coherentIso ⟶ X}
  (hfg : f.edge = g.app _ hom.edge)
  : f.IsIso
  := (isIsoMapHom g).ofEq hfg.symm

end coherentIso

end SSet
