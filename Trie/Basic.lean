
set_option autoImplicit false

universe u
universe v
variable {α : Type u}
variable [DecidableEq α]
variable {β : Type v}

namespace Trie.Abstract

/--
A very abstract idea of a trie data structure. We prove the relevant theorems about
their properties here, and show that more refined implementations behave like these.
-/
inductive Trie (α : Type u) (β : Type v) where
  | node (val : Option β) (c : α → Option (Trie α β)) : Trie α β

namespace Trie


@[simp]
def val : Trie α β → Option β
  | .node v _ => v

@[simp]
def c : Trie α β → α → Option (Trie α β)
  | .node _ c => c

def empty : Trie α β := .node none (fun _ => .none)

def child : Trie α β → α → Trie α β
  | .node _ c, k => (c k).getD empty

def insert (t : Trie α β) : List α → β → Trie α β
  | [], v => .node (some v) t.c
  | k::ks, v => .node t.val fun k' =>
    if k' = k
    then (t.child k).insert ks v
    else t.c k'

def find? (t : Trie α β) : List α → Option β
  | [] => t.val
  | k::ks => match t.c k with
    | none => none
    | some t => t.find? ks

@[simp]
theorem find?_empty (k : List α) : (empty : Trie α β).find? k = none :=  by
  cases k <;> simp [empty, find?]

theorem find?_insert_eq (t : Trie α β) (k : List α) (v : β) :
    (t.insert k v).find? k = some v := by
  induction k generalizing t with
  | nil => simp [insert, find?, val]
  | cons k ks ih =>
    cases t with | _ v' c => simpa [insert, find?, child] using ih _

theorem find?_insert_neq (t : Trie α β) (k k' : List α) (hne : k ≠ k') (v : β) :
    (t.insert k v).find? k' = t.find? k' := by
  induction k generalizing t k' with
  | nil =>
    cases k' with | nil => contradiction | cons k' ks' =>
    cases t with | _ v' c =>
    simp [find?, insert, child]
  | cons k ks ih =>
    cases t with | _ v' c =>
    cases k' with
    | nil => simp [find?, insert, child]
    | cons k' ks' =>
      if hk : k' = k then
        subst k'
        have : ks ≠ ks' := by intro h; apply hne; cases h; rfl
        simp [insert, find?, child, hne, Option.getD]
        simp [ih, this]
        cases c k <;> simp
      else
        simp [insert, find?, child, hk]

end Trie

end Trie.Abstract

theorem Array.drop_data_cons {α : Type _} (as : Array α) (i : Nat) (h : i < as.size) :
  as.data.drop i = as[i] :: as.data.drop (i + 1) := by sorry

theorem Array.drop_data_nil {α : Type _} (as : Array α) (i : Nat) (h : ¬ i < as.size) :
  as.data.drop i = [] := by sorry

@[simp]
theorem Array.extract_data {α} (as : Array α) (i : Nat) (j : Nat) :
  (as.extract i j).data = (as.data.take j).drop i := by sorry

theorem Array.attach {α} (as : Array α) : Array {x : α // x ∈ as} := by sorry

namespace Trie.AbstractArray

/--
Like `Trie.Abstract.Trie`, but the operations (not the implementation!) uses arrays for keys.
-/
abbrev Trie := @Trie.Abstract.Trie

namespace Trie

def empty := @Trie.Abstract.Trie.empty

def insert (t : Trie α β) (ks : Array α) (v : β) : Trie α β := go t 0
  where
  go t i := if h : i < ks.size then
    let k := ks[i]
    .node t.val fun k' =>
      if k' = k
      then go (t.child k) (i + 1)
      else t.c k'
  else
    .node (some v) t.c
  termination_by ks.size - i

derive_induction insert.go

def find? (t : Trie α β) (ks : Array α) : Option β := go t 0
  where
  go t i := if h : i < ks.size then
    match t.c ks[i] with
    | none => none
    | some t => go t (i + 1)
  else
    t.val
  termination_by ks.size - i

derive_induction find?.go

/-
We first specify the operations via their abstract counter-parts on lists.
-/

theorem insert_go_data (t : Trie α β) (ks : Array α) (v : β) (i : Nat) :
    insert.go ks v t i = Abstract.Trie.insert t (ks.data.drop i) v := by
  induction t, i using insert.go.induct (ks := ks) (v := v)
  case case1 t i hi k =>
    intro IH
    unfold insert.go; simp only [hi, ↓reduceDite]
    simp only [Abstract.Trie.insert, Array.drop_data_cons, hi, IH]
  case case2 t i hi =>
    unfold insert.go; simp only [hi, ↓reduceDite]
    simp only [Abstract.Trie.insert, Array.drop_data_nil (h := hi)]

theorem insert_spec (t : Trie α β) (ks : Array α) (v : β) :
    insert t ks v = Abstract.Trie.insert t ks.data v := by simp [insert, insert_go_data]

theorem find?_go_data (t : Trie α β) (ks : Array α)  (i : Nat) :
    find?.go ks t i = Abstract.Trie.find? t (ks.data.drop i) := by
  induction t, i using find?.go.induct (ks := ks)
  case case1 t i hi IH =>
    unfold find?.go; simp only [hi, ↓reduceDite]
    simp only [Abstract.Trie.find?, Array.drop_data_cons, hi, IH]
  case case2 t i hi =>
    unfold find?.go; simp only [hi, ↓reduceDite]
    simp only [Abstract.Trie.find?, Array.drop_data_nil (h := hi)]

theorem find?_spec (t : Trie α β) (ks : Array α) :
    find? t ks = Abstract.Trie.find? t ks.data := by simp [find?, find?_go_data]

/-
Then the actual user-facing theorems follow quickly.
-/

theorem find?_empty (k : Array α) : find? (empty : Trie α β) k = none := by
  simp [find?_spec, Abstract.Trie.find?_empty, empty]

theorem find?_insert_eq (t : Trie α β) (k : Array α) (v : β) :
    (t.insert k v).find? k = some v := by
  simpa [insert_spec, find?_spec] using Abstract.Trie.find?_insert_eq _ _ _

theorem find?_insert_neq (t : Trie α β) (k k' : Array α) (hne : k ≠ k') (v : β) :
    (t.insert k v).find? k' = t.find? k' := by
  have hne' : k.data ≠ k'.data := by intro h; apply hne; cases k; cases k'; simpa
  simpa [insert_spec, find?_spec] using Abstract.Trie.find?_insert_neq _ _ _ hne' _

end Trie

end Trie.AbstractArray


-- Helper functions for associative lists and arrays

namespace AssocList

def upsert (ks : List α) (vs : List β) (k : α) (f : Option β → β) : List α × List β :=
  match ks, vs with
  | k'::ks, v::vs =>
    if k = k' then
      (k'::ks, f (some v) :: vs)
    else
      let (ks, vs) := upsert ks vs k f
      (k'::ks, v::vs)
  | _, _ => ([k], [f none])

def find? (ks : List α) (vs : List β) (k : α) : Option β :=
  match ks, vs with
  | k'::ks, v::vs =>
    if k = k' then
      some v
    else
      find? ks vs k
  | _, _ => none

@[simp]
theorem find?_nil (vs : List β) (k : α) : find? [] vs k = none := by
  simp [find?]

end AssocList

namespace AssocArray

def upsert (ks : Array α) (vs : Array β) (k : α) (f : Option β → β) : Array α × Array β :=
  go 0
  where
  go i :=
    if hi : i < ks.size then
      if hj : i < vs.size then
        if k = ks[i] then
          (ks, vs.modify i (fun v => f (some v)))
        else
          go (i + 1)
      else
        ((ks.extract 0 i).push k, vs.push (f none))
    else
      (ks.push k, (vs.extract 0 i).push (f none))
  termination_by ks.size - i

derive_induction upsert.go

def biDataDrop {α} {β} (pair : Array α × Array β) (i : Nat) : List α × List β :=
  (pair.1.data.drop i, pair.2.data.drop i)

theorem Array.data_ext {α} (a₁ a₂ : Array α) : (a₁ = a₂ ↔ a₁.data = a₂.data) := by
  constructor
  · intro h; subst h; rfl
  · intro h; cases a₁; cases a₂; simpa using h


def upsert_go_spec (ks : Array α) (vs : Array β) (k : α) (f : Option β → β) (i : Nat) :
    upsert.go ks vs k f i =
      let (ks', vs') := AssocList.upsert (ks.data.drop i) (vs.data.drop i) k f;
      ((ks.data.take i ++ ks').toArray, (vs.data.take i ++ vs').toArray) := by
  induction i using upsert.go.induct (ks := ks) (vs := vs) (k := k) (f := f)
  case case1 i hi hj heq =>
    unfold upsert.go; simp only [hi, hj, heq, ↓reduceIte, ↓reduceDite]
    simp [Array.data_ext, AssocList.upsert, Array.drop_data_cons, hi, hj, heq, ↓reduceIte, ↓reduceDite]
    sorry
    -- Stuff about modify
  case case2 i hi hj hneq IH =>
    unfold upsert.go; simp only [hi, hj, hneq, ↓reduceIte, ↓reduceDite]
    simp only [Array.data_ext, AssocList.upsert, Array.drop_data_cons, hi, hj, hneq,
      ↓reduceIte, ↓reduceDite]
    rw [IH]
    simp [Array.data_ext, ← List.take_concat_get, hi, hj]
    sorry -- Needs Array.getElem data
  case case3 i hi hj =>
    have : vs.data.length ≤ i := by sorry -- Needs Array.data_length
    unfold upsert.go; simp only [hi, hj, ↓reduceIte, ↓reduceDite]
    simp [Array.data_ext, AssocList.upsert, Array.drop_data_cons, hi, hj, ↓reduceIte, ↓reduceDite,
      List.take_length_le, List.drop_length_le, this]
  case case4 i hi =>
    have : ks.data.length ≤ i := by sorry -- Needs Array.data_length
    unfold upsert.go; simp only [hi, ↓reduceIte, ↓reduceDite]
    simp [Array.data_ext, AssocList.upsert, Array.drop_data_cons, hi, ↓reduceIte, ↓reduceDite,
      List.take_length_le, List.drop_length_le, this]


def upsert_spec (ks : Array α) (vs : Array β) (k : α) (f : Option β → β) :
    upsert ks vs k f =
      let (ks', vs') := AssocList.upsert ks.data vs.data k f;
      (ks'.toArray, vs'.toArray) := by simp [upsert, upsert_go_spec]

def find? (ks : Array α) (vs : Array β) (k : α) : Option β := go 0
  where
  go i :=
    if hi : i < ks.size then
      if hj : i < vs.size then
        if k = ks[i] then
          some vs[i]
        else
          go (i + 1)
      else
        none
    else
      none
  termination_by ks.size - i

derive_induction find?.go

def find?_go_spec (ks : Array α) (vs : Array β) (k : α) (i : Nat) :
    find?.go ks vs k i = AssocList.find? (ks.data.drop i) (vs.data.drop i) k := by
  induction i using find?.go.induct (ks := ks) (vs := vs) (k := k)
  case case1 i hi hj heq =>
    unfold find?.go; simp only [hi, hj, heq, ↓reduceIte, ↓reduceDite]
    simp [Array.data_ext, AssocList.find?, Array.drop_data_cons, hi, hj, heq, ↓reduceIte, ↓reduceDite]
  case case2 i hi hj hneq IH =>
    unfold find?.go; simp only [hi, hj, hneq, ↓reduceIte, ↓reduceDite]
    simp only [Array.data_ext, AssocList.find?, Array.drop_data_cons, hi, hj, hneq,
      ↓reduceIte, ↓reduceDite, IH]
  case case3 i hi hj =>
    have : vs.data.length ≤ i := by sorry -- Needs Array.data_length
    unfold find?.go; simp only [hi, hj, ↓reduceIte, ↓reduceDite]
    simp only [Array.data_ext, AssocList.find?, Array.drop_data_cons, hi, hj, ↓reduceIte, ↓reduceDite,
      List.drop_length_le, this]
  case case4 i hi =>
    have : ks.data.length ≤ i := by sorry -- Needs Array.data_length
    unfold find?.go; simp only [hi, ↓reduceIte, ↓reduceDite]
    simp only [Array.data_ext, AssocList.find?, Array.drop_data_cons, hi, ↓reduceIte, ↓reduceDite,
      List.drop_length_le, this]

def find?_spec (ks : Array α) (vs : Array β) (k : α) :
    find? ks vs k = AssocList.find? ks.data vs.data k :=
  by simp [find?, find?_go_spec]

@[simp]
theorem find?_nil (vs : Array β) (k : α) : find? #[] vs k = none := by
  simp [find?_spec]

end AssocArray

namespace Trie.Array

/--
A more realistic implementation, using Arrays instead of functions.
-/
inductive Trie (α : Type u) (β : Type v) where
  | node (val : Option β) (ks : Array α) (vs : Array (Trie α β)) : Trie α β

namespace Trie

def empty : Trie α β := .node none #[] #[]

def insert (t : Trie α β) (ks : Array α) (v : β) : Trie α β := go t 0 where
  go | .node val ks' vs, i =>
      if h : i < ks.size then
        let (ks'', vs'') := AssocArray.upsert ks' vs ks[i] fun t? =>
          go (t?.getD empty) (i + 1)
        .node val ks'' vs''
      else
        .node (some v) ks' vs
  termination_by _ i => ks.size - i

noncomputable -- due to Array.attach, which we use for similarity with toAbstractArray
def find? (t : Trie α β) (ks : Array α) : Option β := go t 0 where
  go | .node val ks' vs, i =>
      if h : i < ks.size then
        match AssocArray.find? ks' vs.attach ks[i] with
        | none => none
        | some ⟨t, _⟩  => go t (i + 1)
      else
        val
  termination_by _ i => ks.size - i

derive_induction find?.go

noncomputable -- due to Array.attach
def toAbstractArray : Trie α β → AbstractArray.Trie α β
  | .node val ks vs => .node val fun k =>
    match AssocArray.find? ks vs.attach k with
    | none => none
    | some ⟨t, _⟩ => some t.toAbstractArray
termination_by t => sizeOf t

theorem empty_spec :
    (empty : Trie α β).toAbstractArray = AbstractArray.Trie.empty := by
  simp [toAbstractArray, empty, AbstractArray.Trie.empty]
  rfl

theorem find?_go_spec (t : Trie α β) (ks : Array α) (i : Nat) :
    find?.go ks t i = AbstractArray.Trie.find?.go ks t.toAbstractArray i := by
  induction t, i using find?.go.induct (ks := ks)
  case case1 v ks' vs i hi IH =>
    unfold find?.go
    unfold AbstractArray.Trie.find?.go
    simp only [hi, ↓reduceDite]
    simp only [toAbstractArray, Abstract.Trie.child, Option.getD, Abstract.Trie.c, IH]
    split <;> simp
  case case2 v ks' vs i hi =>
    unfold find?.go
    unfold AbstractArray.Trie.find?.go
    simp only [hi, ↓reduceDite]
    simp only [toAbstractArray, Abstract.Trie.val]
    done

theorem find?_spec (t : Trie α β) (ks : Array α):
    t.find? ks = t.toAbstractArray.find? ks := by
  simp [find?, AbstractArray.Trie.find?, find?_go_spec]


end Trie

end Trie.Array
