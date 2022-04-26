/-
Queremos provar que `a+0=a e 0+a=a` para todo `a` inteiro.

Dividimos em casos
Caso: a+0=a
  a+0=a já dado pelo axioma A2. 

Caso: 0+a=a
Caso base: Considerando `a=1` teremos `0+1=1`.
Passo indutivo: Seja k inteiro tal que `a=k`.
Calculamos: 
1) Para `a=k`
  `0+k=k`   
    `k=k`

2) Para `a=k+1`
   `0+k+1=k+1` 
   `    k=k+1-1`
   `    k=k`   
    

Queremos provar que `a . 1 = a` para todo `a` inteiro.
Calculamos 
  a . 1 = a    
      a = a . 1       //rescrever 1 pela (+)identidade
        = a (0 + 1)   //(.)distributiva 
        = a . 0 + a   //(.)anulador
        = 0 + a       //(+)identidade
        = a   
  -/


import init

--def succ (n : ℕ ) : ℕ 

lemma add_zero (m : ℕ ) : m + 0 = m := rfl
--lemma add_succ (m n : ℕ ) : m + succ n = succ (m + n) := rfl

lemma zero_add (n : ℕ) : 0 + n = n :=
begin 
  induction n with d hd,
    rw add_zero,
    --refl,
  rw nat.add_succ,
  rw hd,
  

end
lemma add_comm (a b : ℕ ) : a + b = b + a :=
begin 
  induction b with d hd,
  { rw zero_add,
    rw add_zero,

  },
  { rw add_succ,
    rw hd,
    rw succ_add,
    refl
  }
end


lemma Zero_Id_R (a : ℕ ): (∀ a, a + 0 = a) :=
begin
  intro a,
  rw add_zero, -- O add_zero aqui faz o papel do nosso Axiom 
 
end


lemma Zero_Id_L (a : ℕ): (∀ a, 0 + a = a) :=
begin
  intro a, 
  rw add_comm,
  rw Zero_Id_R,
  assumption,
end

example (u: ℕ): (∀u, u+0=u) ∧ (∀u, 0+u=u) :=
begin 
  split,
  intro x,
  rw Zero_Id_R,
  assumption,
  intro x,
  rw Zero_Id_L,
  assumption,
end



--example (a b c: ℕ): (∀a b c, c * a = c * b → c = 0 ∨ a = b) →
--                     (∀a b, a * b = 0 → a = 0 ∨  b = 0):= 
theorem lc(a b c: ℕ): (h : c * a = c * b ) : c = 0 ∨ a = b :=
--→
--                     (∀a b, a * b = 0 → a = 0 ∨  b = 0):= 

begin
intros hAabc ha hb h,
left,
rw zero_add h,




sorry,
end


