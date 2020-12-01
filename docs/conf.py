# Configuration file for the Sphinx documentation builder.
#
# This file only contains a selection of the most common options. For a full
# list see the documentation:
# https://www.sphinx-doc.org/en/master/usage/configuration.html

# -- Path setup --------------------------------------------------------------

# If extensions (or modules to document with autodoc) are in another directory,
# add these directories to sys.path here. If the directory is relative to the
# documentation root, use os.path.abspath to make it absolute, like shown here.
#
# import os
# import sys
# sys.path.insert(0, os.path.abspath('.'))


# -- Project information -----------------------------------------------------

# source_suffix = ['.rst', '.md']
source_suffix = '.rst'

# The master toctree document.
master_doc = 'index'

project = 'überXMHF Documentation'
copyright = '2020, Amit Vasudevan'
author = 'https://uberxmhf.org'
release = 'Version: 6.0.0'

# -- General configuration ---------------------------------------------------

# Add any Sphinx extension module names here, as strings. They can be
# extensions coming with Sphinx (named 'sphinx.ext.*') or your custom
# ones.

extensions = [
    'sphinx.ext.autosectionlabel',
    'sphinxjsondomain'
]
autosectionlabel_prefix_document = True
autosectionlabel_maxdepth = 4



# Add any paths that contain templates here, relative to this directory.
templates_path = ['_templates']

# List of patterns, relative to source directory, that match files and
# directories to ignore when looking for source files.
# This pattern also affects html_static_path and html_extra_path.
exclude_patterns = ['_themes', '_temp']


# -- Options for HTML output -------------------------------------------------

# The theme to use for HTML and HTML Help pages.  See the documentation for
# a list of builtin themes.
#

html_theme = 'rtd_uberspark'
html_theme_path = ["_themes", ]
html_theme_options = {
    'repository' : 'https://github.com/uberspark/uberxmhf',
    'style_external_links': True,
    'collapse_navigation' : False,
    'navigation_depth': 4,

    'current_language' : 'en',
    'current_version' : 'latest',

    'languages' : {
        'en' : ''
    },

    'versions' : {
        'latest' : ''
    },

    'downloads' : {
        'PDF' : ''
    }

}    


# -- Options for LaTeX output ---------------------------------------------

latex_engine = 'pdflatex'
latex_elements = {
    'papersize': 'letterpaper',
    'figure_align':'htbp',
    'pointsize': '12pt',
}

# Grouping the document tree into LaTeX files. List of tuples
# (source start file, target name, title,
#  author, documentclass [howto, manual, or own class]).
latex_documents = [
    (master_doc, 'uberxmhf_documentation.tex', project,
     author, 'manual')
]



