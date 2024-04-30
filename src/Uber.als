module src

// Criação de Usuários 

abstract sig User {
    region: one Region
}

one sig Estudante, Professor, Servidor extends Usuario{}

sig Motorista in User {}
sig Passageiro in User {}

// Débitos e Créditos de motoristas e Passageiros

sig Debito in Passageiro {}
sig Credito in Motorista {}

// Criação das Regiões

abstract sig Region extends Region {}
one sig Centro, Oeste, Leste, Norte, Sul extends Region {}

// Criação dos Horários de Corridas

abstract sig Horario {}

// Definição para horários de Ida
abstract sig Ida extends Horario {}

// Definição para horários de Saída
abstract sig Saida extends Horario {}

one sig 8, 10, 14, 16, extends Ida {}
one sig 10, 12, 16, 18 extends Saida {}

// Criação da corrida

sig Uber {
    origem : one Region
    horarioSaida : one Horario
    motorista : one Motorista
    passageiros : set Passageiro
}


// Predicados para validar o código

// Valida se o usuário é professor, estudante ou servidor
pred checkUsers[u:Uber] {
    u.motorista in Aluno + Professor + Servidor
    
    all p: u.passageiros | p in Aluno + Professor + Servidor
}

// Valida se o número de passageiros está dentro do limite
pred checkPassageiros[u:Uber] {
    #u.passageiros > 0
    #u.passageiros <= 3
}

// Verifica se o motorista não é um passageiro
pred checkMotorista[u:Uber] {
    #u.motorista !in u.passageiros
}

// Verifica se as regiões são as mesmas
pred checkRegion[u:uber] {
    u.motorista.region = u.region

    all p: u.passageiros |
        p.region = u.region
        p.region = u.motorista.region
}


fact {
    all u:Uber | checkUsers[u] && checkPassageiros[u] && 
        checkMotorista[u] && checkRegion[u]
}

fact {
    all 
}

