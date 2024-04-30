module src

// Criação de Usuários 

abstract sig User {
    region: one Region
}

one sig Estudante, Professor, Servidor extends User{}

sig Motorista in User {}
sig Passageiro in User {}

// Débitos e Créditos de motoristas e Passageiros

sig Debito in Passageiro {}
sig Credito in Motorista {}

// Criação das Regiões

abstract sig Region{}
one sig Centro, Oeste, Leste, Norte, Sul extends Region {}

// Criação dos Horários de Corridas

abstract sig Horario {}

one sig ida_8, ida_10, ida_14, ida_16 extends Horario {}
one sig saida_10, saida_12, saida_16, saida_18 extends Horario {}

// Criação da corrida

sig Uber {
    region: one Region,
    horarioSaida: one Horario,
    motorista: one Motorista,
    passageiros: set Passageiro
}


// Predicados para validar o código

// Valida se o usuário é professor, estudante ou servidor
pred checkUsers[u:Uber] {
    u.motorista in Estudante + Professor + Servidor
    
    all p: u.passageiros | p in Estudante + Professor + Servidor
}

// Valida se o número de passageiros está dentro do limite
pred checkPassageiros[u:Uber] {
    #u.passageiros > 0
    #u.passageiros <= 3
    
    all p: u.passageiros |
        (p not in Motorista)
}

// Verifica se o motorista não é um passageiro
pred checkMotorista[u:Uber] {
    u.motorista !in u.passageiros
    u.motorista not in Passageiro
    #u.motorista = 1
}

// Verifica se as regiões são as mesmas
pred checkRegion[u: Uber] {
    u.motorista.region = u.region

    all p: u.passageiros |
        (p.region = u.region) and (p.region = u.motorista.region)
}


fact {
    all u:Uber | checkUsers[u] && checkPassageiros[u] && 
        checkMotorista[u] && checkRegion[u]
}

fact { all p:Passageiro | one d:Debito | d in p }
fact { all m:Motorista | one c:Credito | c in m }


run{} for 5
