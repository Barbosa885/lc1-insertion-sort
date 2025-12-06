# Projeto de Logica Computacional 1: Ordenacao por Insercao

Este repositorio contem o projeto final da disciplina de Logica Computacional 1 (2025/1), focado na formalizacao e prova da correcao do algoritmo de ordenacao por insercao (Insertion Sort) utilizando o assistente de provas Coq.

## Estrutura do Projeto

* insertion_sort.v: Codigo fonte em Coq contendo a implementacao do algoritmo e as provas de correcao.
* report.tex: Relatorio tecnico do projeto em formato LaTeX.
* referencias.bib: Arquivo de bibliografia para o relatorio.

## Pre-requisitos

Para compilar e verificar o projeto, voce precisara das seguintes ferramentas:

* Coq (versao 8.10 ou superior recomendada)
* LaTeX (para compilar o relatorio)

## Como Compilar

### Codigo Coq

Para verificar as provas do arquivo Coq, execute o seguinte comando no terminal:

coqc insertion_sort.v

Se nao houver saida de erro, significa que todas as provas foram verificadas com sucesso.

### Relatorio LaTeX

Para gerar o PDF do relatorio, utilize o `pdflatex` e o `bibtex`:

1. pdflatex report.tex
2. bibtex report
3. pdflatex report.tex
4. pdflatex report.tex

## Autores

* Gustavo Barbosa de Almeida
* Vitor Camilo Lemos
* Thiago Silva Ribeiro
